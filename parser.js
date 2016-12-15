// Lexer; turns a string or iterable into a sequence of tokens
function* lex(str){
  if((typeof str) === 'string'){
    str = function*(str){
          yield* str.split('');
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