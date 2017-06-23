class Graph {
  constructor(){
    this.starts = new Map();
    this.ends = new Map();
  }

  addEdge(to,from){
    if(!this.starts.has(from))this.starts.set(from,new Set());
    this.starts.get(from).add(to);
    if(!this.ends.has(to))this.ends.set(to,new Set());
    this.ends.get(to).add(from);
  }

  removeEdge(to,from){
    if(this.starts.has(from))this.starts.get(from).delete(to);
    if(this.ends.has(to))this.ends.get(to).delete(from);
  }

  goesTo(to){
    if(!this.ends.has(to))this.ends.set(to,new Set());
    return this.ends.get(to);
  }

  comesFrom(from){
    if(!this.starts.has(from))this.starts.set(from,new Set());
    return this.starts.get(from);
  }

  removeNode(node){
    if(this.starts.has(node)){
      for(let end of this.starts.get(node)){
        this.ends.get(end).delete(node);
      }
      this.starts.delete(node);
    }
    if(this.ends.has(node)){
      for(let start of this.ends.get(node)){
        this.starts.get(start).delete(node);
      }
      this.ends.delete(node);
    }
  }
}

// For simplifying proofs (pruning unneeded deductions)
function treeify(steps,i=0,graph=new Graph(),lookup=new Map()){
  var sub = new Set();
  for(let step of steps){
    i++;
    let line = LINE(step);
    line.i = i;
    sub.add(line);
    if(step.type === 'show'){
      line.type = 'show';
      [line.sub,_,i] = treeify(step.steps,i,graph,new Map(lookup));
      let s = str(step.exp);
      if(!lookup.has(s))lookup.set(s,line);
      for(let comp of complete(line.sub,step.exp)){
        graph.addEdge(line,comp);
      }
      continue;
    }
    line.type = 'normal';
    if(step.type === 'repetition'){
      if(!lookup.has(str(step.exp))){
        throw "NOOOOOOO";
      }
      graph.addEdge(line,lookup.get(str(step.exp)));
    }
    if(step.type === 'assumption'){
      let s = str(step.exp);
      if(!lookup.has(s))lookup.set(s,line);
    }
    if(step.type === 'derived'){
      for(let exp of step.from){
        graph.addEdge(line,lookup.get(str(exp)));
      }
      let s = str(step.exp);
      if(!lookup.has(s))lookup.set(s,line);
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
    return findExp(s,exp)||findExp(s,exp.rhs)||contradiction(s);
  }
  return contradiction(s);
}

function flood(line,graph,out = new Set()){
  out.add(line);
  for(let newline of graph.goesTo(line)){
    flood(newline,graph,out);
  }
  return out;
}

function filterProof(proof,graph,lines){
  for(let line of proof){
    if(!lines.has(line)){
      proof.delete(line);
      graph.removeNode(line);
    }
    if(line.type === 'show'){
      filterProof(line.sub,graph,lines);
    }
  }
}

function eliminateShows(proof,graph,toplevel=false){
  for(let line of proof){
    if(line.type === 'show'){
      eliminateShows(line.sub,graph);
      let depends = [...graph.goesTo(line)];
      let assumpts = depends.filter(l=>l.step.type==='assumption');
      
      if(depends.length == 2 && assumpts.length){
        let assumpt = assumpts[0];
        let other = depends.filter(l=>l.step.type!=='assumption')[0];
        if([...graph.comesFrom(assumpt)].length > 1 || str(other.step.exp) !== str(line.step.exp))continue;
        // if its an indirect derivation that could be direct
        console.log('Only use of', assumpt, 'is the above show line:',line,'. Complementing line is',other);
        line.type = 'block';
        for(let use of graph.comesFrom(line)){
          graph.addEdge(other,use);
        }
        graph.removeNode(line);
        assumpt.type = 'none';
      }else if(!toplevel && ![...line.sub.keys()].filter(l=>l.step.type==='assumption').length && depends.length === 1 ){ // if its a direct derivation just inline
        let other = depends[0];
        if(str(other.step.exp) !== str(line.step.exp))continue;
        line.type = 'block';
        for(let use of graph.comesFrom(line)){
          graph.addEdge(other,use);
        }
        graph.removeNode(line);
      }
    }
  }
}

function reformProof(proof){
  var out = [];
  for(let line of proof){
    if(line.type === 'show'){
      out.push({type:'show', exp: line.step.exp,steps:reformProof(line.sub)});
    }else if(line.type === 'block'){
      out.push(...reformProof(line.sub));
    }else if(line.type !== 'none'){
      out.push(line.step);
    }
  }
  return out;
}

function pruneSteps(steps){
  var [proof, graph] = treeify(steps);
  var sub = flood([...proof.keys()][0],graph);
  filterProof(proof,graph,sub);
  eliminateShows(proof,graph,top);
  steps = reformProof(proof);
  
  // run it one more time to clean up after inlines
  // this could be in a while, but 2 seems to work well enough
  [proof, graph] = treeify(steps);
  sub = flood([...proof.keys()][0],graph);
  filterProof(proof,graph,sub);
  eliminateShows(proof,graph,top);
  return reformProof(proof);
}