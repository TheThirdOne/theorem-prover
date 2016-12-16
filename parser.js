// Lexer; turns a string or iterable into a sequence of tokens
function* lex(str){
  if((typeof str) === 'string'){
    str = function*(str){
          for(let c of str.split('')){
            yield c;
          }
          while(true){
            yield ')';
          }
        }(str);
  }
  while(true){
    var a = str.next().value;
    switch(a){
      case 'v':
      case '^':
      case '~':
      case '(':
      case ')':
        yield {token:a};
        break;
      case '<':
        if(str.next().value === '-' && str.next().value === '>'){
          yield {token:'<->'};
        }else{
          throw "ERROR unexpected value";
        }
        break;
      case '-':
        if(str.next().value === '>'){
          yield {token:'->'};
        }else{
          throw "ERROR unexpected value";
        }
        break;
      default:
        yield {token:'variable',value:a};
    }
  }
}

// Constructs a parse tree from tokens
// Warning: Not very robust
function parse(l){
  var n = l.next().value;
  if(n.token === 'variable'){
    return {type: 'variable', value: n.value};
  }
  if(n.token === '~'){
    return NOT(parse(l));
  }
  if(n.token !== '('){
    throw "Expected (";
  }
  
  var lhs = parse(l);
  
  n = l.next().value;
  if(n.token !== '->' && n.token !== 'v' && n.token !== '^' && n.token !== '<->' ){
    throw "Expected a binary connective";
  }
  var c = n.token;
  var rhs = parse(l);

  n = l.next().value;
  if(n.token !== ')'){
    throw "Expected )";
  }
  return {type: 'binary', lhs:lhs, rhs:rhs, connective:c};
}

// Helpers to construct various connectives
function NOT(a){
  return {type:'not',lhs:a};
}
function IF(lhs,rhs){
  return {type:'binary',connective:'->',
            lhs:lhs,rhs:rhs};
}
function OR(lhs,rhs){
    return {type:'binary',connective:'v',
            lhs:lhs,rhs:rhs};
}
function AND(lhs,rhs){
    return {type:'binary',connective:'^',
            lhs:lhs,rhs:rhs};
}

var precedence = {'~':3,'^':2,'v':2,'->':1,'<->':0};
function flexibleParse(l){
  let stack = [];
  let next = l.next().value;
  if(next.token === '('){
    stack.push({done:true,exp:flexibleParse(l)});
  }else if(next.token === 'variable'){
    stack.push({done:true,exp:{type: 'variable', value: next.value}});
  }else if(next.token === '~'){
    stack.push({done:false,type:'not'});
  }else if(next.token === '->' || next.token === 'v' || next.token === '^' || next.token === '<->' || next.token === ')'){
    throw "Did not expect the token: " + next.token + '. Expected a (, ~ or variable.'
  }
  // Hacky shit because I want the generator to not be ended after we break from the loop
  for(let next = l.next(); !next.done; next = l.next()){
    next = next.value;
    let last = stack[stack.length-1];
    if(next.token === ')'){
      break;
    }
    if(next.token === '->' || next.token === 'v' || next.token === '^' || next.token === '<->'){
      if(!last.done){
        throw "Did not expect the token: " + next.token + '. Expected a (, ~ or variable.';
      }
      let lhs = last.exp;
      stack.pop();
      for(let i = stack.length-1; i >= 0; i--){
        if(precedence[next.token] < precedence[stack[i].type]){
          lhs = {type:'binary',connective:stack[i].type,lhs:stack[i].lhs,rhs:lhs};
          stack.pop();
        }else{
          break;
        }
      }
      stack.push({done:false,type:next.token,lhs:lhs});
    }else if(next.token === '~'){
      if(last.done){
        throw "Missing connective before ~";
      }
      stack.push({done:false,type:'not'});
    }else if(next.token === 'variable'){
      if(last.done){
        throw "Missing connective before new variable: " + next.value;
      }
      stack.push({done:true,exp:{type: 'variable', value: next.value}});
    }else if(next.token === '('){
      if(last.done){
        throw "Missing connective before new (";
      }
      stack.push({done:true,exp:flexibleParse(l)});
    }
  }
  var last = stack[stack.length-1];
  if(!last.done){
    throw "Unexpected end to expression. Expected another complete expression before it"
  }
  var exp = last.exp;
  for(let i = stack.length-2; i >= 0; i--){
    if(stack[i].done){
      throw "Missing connective";
    }
    if(exp.type === 'not'){
      exp = not(exp);
    }else{
      exp = {type:'binary',connective:stack[i].type,lhs:stack[i].lhs,rhs:exp};
    }
  }
  return exp;
}