// General helpers
function contra(a,b){
  a = simplify(a), b = simplify(b);
  return a.i%2 !== b.i%2 && equal(a.base,b.base);
}
function equiv(a,b){
  a = simplify(a), b = simplify(b);
  return a.i%2 === b.i%2 && equal(a.base,b.base);
}
function negofConnective(exp){
  exp = simplify(exp);
  return exp.i%2 === 1 && exp.base.type === 'binary';
}
function connnective(exp){
  exp = simplify(exp);
  return exp.i%2 === 0 && exp.base.type === 'binary';
}
function simplify(a){
  if(a.type === 'not'){
    let b = simplify(a.lhs);
    b.i++;
    return b;
  }else{
    return {i:0, base:a};
  }
}
function equal(a,b){
  if(a.type !== b.type){
    return false;
  }
  if(a.type === 'variable'){
    return a.value === b.value;
  }
  if(a.type === 'not'){
    return equal(a.lhs,b.lhs);
  }
  return a.connective===b.connective&&equal(a.lhs,b.lhs)&&equal(a.rhs,b.rhs);
}
function finished(truths){
  return !!truths.filter(a=>truths.filter(b=>contra(a,b)).length).length;
}


// Helpful for generating expressions
function toConditional(exp){
  if(exp.type === 'variable'){
    return exp;
  }
  if(exp.type === 'not'){
    return NOT(toConditional(exp.lhs));
  }
  if(exp.connective === 'v'){
    return {type:'binary',connective:'->',
            lhs:NOT(toConditional(exp.lhs)),rhs:toConditional(exp.rhs)};
  }
  if(exp.connective === '^'){
    return NOT({type:'binary',connective:'->',
            lhs:toConditional(exp.lhs),rhs:NOT(toConditional(exp.rhs))});
  }
  if(exp.connective === '<->'){
    return toConditional(AND(IF(exp.lhs,exp.rhs),IF(exp.rhs,exp.lhs)));
  }
  return {type:'binary',connective:exp.connective,
  lhs:toConditional(exp.lhs),rhs:toConditional(exp.rhs)};
}

var pl = s=>parse(lex(s));// Helpful for generating expressions
