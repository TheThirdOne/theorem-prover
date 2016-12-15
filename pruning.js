// For simplifying proofs (pruning unneeded deductions)
function treeify(steps,i=0,graph=new Map(),lookup=new Map()){
  var sub = new Set();
  for(let step of steps){
    i++;
    let line = LINE(step);
    line.i = i;
    sub.add(line);
    if(step.type === 'show'){
      line.type = 'show';
      [line.sub,_,i] = treeify(step.steps,i,graph,new Map(lookup));
      lookup.set(str(step.exp),line);
      graph.set(line,complete(line.sub,step.exp));
      continue;
    }
    line.type = 'normal';
    if(step.type === 'repetition'){
      if(!lookup.has(str(step.exp))){
        throw "NOOOOOOO";
      }
      graph.set(line,[lookup.get(str(step.exp))]);
    }
    if(step.type === 'assumption'){
      lookup.set(str(step.exp),line);
    }
    if(step.type === 'derived'){
      graph.set(line,step.from.map(a=>lookup.get(str(a))));
      lookup.set(str(step.exp),line);
    }
  }
  return [sub,graph,i-1];
}
function LINE(step){
  return {step:step};
}
function contradiction(s){
  for(let line of s.keys()){
    let contradictions = [...s.keys()].filter(l2=>equal(l2.step.exp,NOT(line.step.exp)));
    if(contradictions.length){
      return [line,contradictions[0]];
    }
  }
  throw "CONTRADICTION NOT FOUND";
}
function findExp(s,exp){
  for(let line of s){
    if(equal(line.step.exp,exp)){
      return [line];
    }
  }
  return false;
}
function complete(s,exp){
  if(exp.type === 'binary' && (exp.connective === '<->' || exp.connective === '^' ||  exp.connective === 'v')){
    return findExp(s,exp)||contradiction(s);
  }
  if(exp.type === 'binary' && exp.connective === '->'){
    return findExp(s,exp.rhs)||contradiction(s);
  }
  return contradiction(s);
}

function flood(line,graph,out = new Set()){
  out.add(line);
  if(graph.has(line)){
    for(let newline of graph.get(line)){
      flood(newline,graph,out);
    }
  }
  return out;
}

function filterProof(proof,lines){
  for(let line of proof){

    if(!lines.has(line)){
      proof.delete(line);
    }
    if(line.type === 'show'){
      filterProof(line.sub,lines);
    }
  }
}

// Not quite ready for use, needs a test to make sure cascading elimination (or multiline bottom level shows) works
function eliminateShows(proof,graph){
  outer:
  for(let line of proof){
    if(line.type === 'show'){
      eliminateShows(line.sub,graph);
      let depends = graph.get(line);
      if(depends.length > 1 && depends.filter(l=>l.step.type==='assumption').length){
        let [other,assumpt] = depends;
        for(let [key,value] of graph){
          if(value === assumpt && key !== line){
            continue outer;
          }
        }
        console.log('Only use of', assumpt, 'is the above show line:',line,'. Complementing line is',other);
        line.type = 'normal';
        line.step = other.step;
      }
    }
  }
}

function reformProof(proof){
  var out = [];
  for(let line of proof){
    if(line.type === 'show'){
      out.push({type:'show', exp: line.step.exp,steps:reformProof(line.sub)});
    }else{
      out.push(line.step);
    }
  }
  return out;
}

function pruneSteps(steps){
  var [proof, graph] = treeify(steps);
  var sub = flood([...proof.keys()][0],graph);
  filterProof(proof,sub);
  return reformProof(proof)
}