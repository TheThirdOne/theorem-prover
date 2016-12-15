// For generating strings of the results
function str(a){
  if(a.type === 'not'){
    return '~' + str(a.lhs);
  }
  if(a.type === 'variable'){
    return a.value;
  }
  if(a.type === 'binary'){
    return '('+str(a.lhs)+a.connective+str(a.rhs)+')';
  }
}
function writeProof(steps,i=1,indent=' ',map=new Map()){
  var out = [];
  var reasons = [];
  for(let step of steps){
    let s = '', r = '';
    if(step.type === 'show'){
      out.push(indent + 'Show ' + str(step.exp));
      reasons.push('');
      [s, r, k] = writeProof(step.steps,i+1,indent+' | ',new Map(map));
      map.set(str(step.exp),i);
      i = k;
      out.push(...s);
      reasons.push(...r);
      continue;
    }
    if(step.type === 'repetition'){
      s += indent + str(step.exp);
      if(!map.has(str(step.exp))){
        throw "NOOOOOOO";
      }
      r = step.reason + ' ' + map.get(str(step.exp));
      map.set(str(step.exp),i);
    }
    if(step.type === 'assumption'){
      map.set(str(step.exp),i);
      s += indent + str(step.exp);
      r = step.reason;
    }
    if(step.type === 'derived'){
      map.set(str(step.exp),i);
      s += indent + str(step.exp);
      r = step.reason + ' ' + (step.from.map(a=>map.get(str(a))).join(', '));
    }
    out.push(s);
    reasons.push(r);
    i++;
  }
  return [out,reasons,i];
}
function prettify(steps,reasons){
  var max = 0, out = '';
  for(let step of steps){
    max = Math.max(step.length,max)
  }
  var digits = Math.ceil(Math.log10(steps.length));
  for(let [i,step] of steps.entries()){
    out += ((new Array(1+digits-Math.ceil(Math.log10(i+2))).join(' '))+(i+1)+'. ')+
            step + (new Array(max-step.length+3).join(' ')) + reasons[i] + '\n';
  }
  return out;
}