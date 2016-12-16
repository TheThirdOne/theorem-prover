function vars(exp,s=new Set()){
  if(exp.type === 'variable'){
    s.add(exp.value);
  }else if(exp.type === 'not'){
    vars(exp.lhs,s);
  }else{
    vars(exp.lhs,s);
    vars(exp.rhs,s);
  }
  return s
}

function *states(vs,i=0){
  if(i >= vs.length){
    yield new Map();
  }else{
    let v = vs[i];
    for(let option of states(vs,i+1)){
      option.set(v,true);
      yield option;
      option.set(v,false);
      yield option;
    }
  }
}

function E(exp,truths){
  if(exp.type === 'variable'){
    return truths.get(exp.value);
  }else if(exp.type === 'not'){
    return !E(exp.lhs,truths);
  }else{
    switch(exp.connective){
      case '^':
        return E(exp.lhs,truths)&&E(exp.rhs,truths);
      case 'v':
        return E(exp.lhs,truths)||E(exp.rhs,truths);
      case '<->':
        return E(exp.lhs,truths)===E(exp.rhs,truths);
      case '->':
        return !E(exp.lhs,truths)||E(exp.rhs,truths);
    }
    console.error('You shouldn\'t be here');
  }
}

function findWrong(exp){
  var v = vars(exp);
  for(let bindings of states([...v])){
    if(!E(exp,bindings)){
      return bindings;
    }
  }
  return false;
}