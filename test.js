function testFormal(exp){
  var formal, loose;
  try{
    formal = parse(lex(exp));
    loose = flexibleParse(lex(exp));
  }catch(e){
    console.warn('On parsing: ' + exp + 'either parse or flexibleParse errored');
    return false;
  }
  if(!equal(formal,loose)){
    console.warn("Mismatch: formal: " + str(formal) + ', loose: ' + str(loose));
    return false;
  }
  if(str(formal)!==exp){
    console.warn("Misparse: formal parsing gave:" + str(formal) + ' for parsing: ' + exp);
    return false;
  }
  return true;
}

function testInformal(exp){
  var [l,f] = exp.split(':');
  var loose;
  try{
    loose = flexibleParse(lex(l));
  }catch(e){
    console.warn('On parsing: ' + l + 'flexibleParse errored');
    return false;
  }
  if(str(loose)!==f){
    console.warn("Misparse: loose parsing gave:" + str(loose) + ' for parsing: ' + l + 'should have given: ' + f);
    return false;
  }
  return true;
}


function testParsing(){
  var formal = '(p->q),(q->~p),(p^q),(~pvq),(p<->q),((pv~q)->~(~p^~q))'.split(',').map(testFormal);
  var informal = '~p^q->pvq:((~p^q)->(pvq)),a->b->c:(a->(b->c))'.split(',').map(testInformal);
}