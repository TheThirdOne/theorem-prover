// Simple prover that follows thease rules (Always use above rules first)
// 1. To derive a conditional, assume the antecedent, then derive the consequent
// 2. To derive a conjuction, derive the conjucts, then use adjunction
// 3. To derive a biconditional, derive the two corresponding conditionals, then use conditional biconditional
// 4. To derive anyting else, use indirect derivation
// 5. Whenever an expression follows from the antecedent lines (allowing DN to be inserted as needed) by MP, MT, S, or BC, enter that as a line
// 6. Use DN to reduce doubled negations of conjuctions, biconditionals, and conditionals to more useful forms
// 7. In an indirect derivation, if a negation of a conditional, conjuction or biconditional occurs, derive the base version.
// 8. When a conditional occurs without the ability to use MP or MT, derive the antecedent
function prove(thm, truths=[], hints=[]){
  console.log('show ', str(thm));
  var steps = [];
  var used = [];
  if(thm.type === 'binary' && thm.connective === '->'){
    // Use conditional derivation to derive a conditional
    
    // Shortcut: if the consequent is already there, just repeat it
    if(truths.filter(exp=>equiv(exp,thm.rhs)).length){
      if(!truths.filter(exp=>equal(exp,thm.rhs)).length){
        steps = reduction(truths.filter(exp=>equiv(exp,thm.rhs))[0],thm.rhs);
      }else{
        steps.push({type:'repetition', reason:'repetition', exp:thm.rhs});
      }
      console.log('Taking shortcut on',str(thm),'using',steps.map(s=>str(s.exp)));
      [{type:'show', exp:thm, steps:steps}];
    }
    return [{type:'show', exp: thm,steps:[{type:'assumption', reason:'assumption (cd)', exp: thm.lhs},...prove(thm.rhs,[thm.lhs,...truths],[...hints])]}];
  }else if(thm.type === 'binary' && thm.connective === '<->'){
    // Show the subparts and then use conditional biconditional to derive biconditionals
    let forward = IF(thm.lhs,thm.rhs);
    let backward = IF(thm.rhs,thm.lhs);
    let steps = [...prove(forward,[...truths],[...hints]),                    // Prove the forward case
                 ...prove(backward,[...truths],[...hints]),                   // Then prove the backward case
                {type:'derived',reason:'CB',exp:thm,from:[forward,backward]}];// Then combine them
    return [{type:'show', exp: thm,steps:steps}];
  }else if(thm.type === 'binary' && thm.connective === '^'){
    // Show the subparts and then use adjunction to derive conjunctions
    let steps = [...prove(thm.lhs,[...truths],[...hints]),                    // Prove the left side
                 ...prove(thm.rhs,[...truths],[...hints]),                    // Then prove the right case
                {type:'derived',reason:'ADJ',exp:thm,from:[thm.lhs,thm.rhs]}];// Then combine them
    return [{type:'show', exp: thm,steps:steps}];
  }else if(thm.type === 'binary' && thm.connective === 'v'){
    // Trick the system into proving something harder than it knows how to do
    let cdForm = IF(NOT(thm.lhs),thm.rhs);
    let miniProof = prove(cdForm,[...truths],[...hints])[0]; // prove ~lhs -> rhs
    miniProof.exp = thm.lhs;                                 // then pretend it was actually an indirect derivation
    miniProof.steps[0].reason = 'assumption (id)';           // Then make an actual contradiction
    miniProof.steps.push({type:'derived',reason:'ADD',exp: thm,from:[thm.rhs]},{type:'repetition', reason:'repetition',exp: NOT(thm)});

    // Build a simple proof around that trick
    let steps = [{type:'assumption', reason:'assumption (id)', exp: NOT(thm)},
                 miniProof,
                 {type:'derived',    reason:'ADD',             exp: thm,      from:[thm.lhs]}];
    return [{type:'show', exp: thm,steps:steps}];
  }else{
    // Otherwise use indirect derivation
    steps.push({type:'assumption', reason:'assumption (id)', exp: NOT(thm)});
    truths.push(NOT(thm));
    used.push(NOT(thm));
  }
  
  // Use Modus Ponens and Modus Tollens until they can no longer be applied or the derivation is finished
  var newsteps, newtruths;
  do{
    [newsteps,newtruths] = deduce(truths,used);
    steps.push(...newsteps);
    truths.push(...newtruths);
    used.push(...newtruths);
    if(!newsteps.length&&!finished(truths)){
      // If modus ponens and tollens weren't enough look for a negated connective then prove the base version
      let negated = truths.filter(exp=>negofConnective(exp)&&!hints.filter(hint=>equiv(hint,exp)).length);
      if(negated.length===0){
        // If there aren't any of those try deriving an antecendent to a conditional
        let unusedConds = truths.filter(exp=>exp.type === 'binary'&&exp.connective === '->'        // Look for a conditional
                            &&!truths.filter(ant=>equiv(ant,exp.lhs)||contra(ant,exp.lhs)).length  // That does not have its antecendent or negation of its antecedent fufilled
                            &&!hints.filter(hint=>equiv(hint,exp)).length);                        // And is not in the hints
        if(unusedConds.length===0){
          let unusedOrs = truths.filter(exp=>exp.type === 'binary'&&exp.connective === 'v'         // Look for a disjunction
                            &&!truths.filter(ant=>equiv(ant,exp.lhs)||equiv(ant,exp.rhs)).length   // That does not have either side fufilled
                            &&!hints.filter(hint=>equiv(hint,exp)).length);                        // And is not in the hints
          if(unusedOrs.length===0){
            console.log(truths.map(str))
            throw "Missing Hint (or not true) (Hard)";
          }
          console.log('Hint: Negation of side of a disjunction');
          newsteps = prove(NOT(unusedOrs[0].lhs),[...truths],[unusedOrs[0],...hints]);
          console.log(str(NOT(unusedOrs[0].lhs)),[...truths].map(str),[unusedOrs[0],...hints].map(str));
          steps.push(...newsteps);
          truths.push(NOT(unusedOrs[0].lhs));
          hints.push(unusedOrs[0]);
        }else{
          console.log('Hint: Antecdent to conditional');
          newsteps = prove(unusedConds[0].lhs,[...truths],[unusedConds[0],...hints]);
          steps.push(...newsteps);
          truths.push(unusedConds[0].lhs);
          hints.push(unusedConds[0]);
        }
      }else{
        console.log('Hint: Negated connective');
        negated = negated[0];
        if(!used.filter(exp=>equal(exp,negated)).length){
          steps.push({type:'repetition', reason:'repetition', exp:negated});
        }
        let base = simplify(negated).base;
        steps.push(...reduction(negated, NOT(base)));
        steps.push(...prove(base,[...truths],[negated,...hints]));
        return [{type:'show', exp: thm, steps:steps}];
      }
    }
  }while(newsteps.length&&!finished(truths));
  
  if(!finished(used)){
    // If the contradiction isn't inside the immediate derivation, repeat the necessary lines
    let part = used.filter(a=>truths.filter(b=>contra(a,b)).length);
    if(part.length === 0){
      part = truths.filter(a=>truths.filter(b=>contra(a,b)).length);
      steps.push({type:'repetition', reason:'repetition', exp:part[0]});
    }
    let second = truths.filter(b=>contra(part[0],b));
    if(second.length === 0){
      throw "NOOOOOOOOOOOOOOOOO";
    }
    steps.push({type:'repetition', reason:'repetition', exp:second[0]});
  }
  
  return [{type:'show', exp: thm, steps:steps}];
}

// Main powerhouse of the prover, encodes Modus ponens, modus tollens, simplification, biconditional conditional, and modus tollendo ponens
// Generates steps to produce everything that can be done with a single invokation of the above rules
function deduce(truths, listed){
  // Use MP and MT
  var conds = truths.filter(exp=>exp.type === 'binary' && exp.connective === '->');
  var mp = conds.filter(cd=>truths.filter(ant=>equiv(cd.lhs,ant)).length);
  mp = mp.filter(cd=>!truths.filter(tr=>equiv(cd.rhs,tr)).length);
  var mt = conds.filter(cd=>truths.filter(con=>contra(cd.rhs,con)).length);
  mt = mt.filter(cd=>!truths.filter(tr=>equiv(NOT(cd.lhs),tr)).length);

  var steps = [];
  for(let cd of mp){
    for(let exp of truths){
      if(equiv(exp,cd.lhs)){
        steps.push(...reduction(exp,cd.lhs));
        break;
      }
    }
    steps.push({type: 'derived', reason:'MP',exp:cd.rhs,from:[cd.lhs,cd]});
  }
  for(let cd of mt){
    for(let exp of truths){
      if(contra(exp,cd.rhs)){
        steps.push(...reduction(exp,NOT(cd.rhs)));
        break;
      }
    }
    steps.push({type: 'derived', reason:'MT',exp:NOT(cd.lhs),from:[NOT(cd.rhs),cd]});
  }
  
  // Double negate to get connectives free
  var DNConns = truths.filter(exp=>exp.type === 'not'&&connnective(exp)&&
                !truths.filter(base=>equal(base,simplify(exp).base)).length);
  for(let dncd of DNConns){
    let base = simplify(dncd).base;
    steps.push(...reduction(dncd,base));
  }
  
  // Use biconditional conditional to get conditionals free
  var biconds = truths.filter(exp=>exp.type === 'binary' && exp.connective === '<->');         // Find biconditionals
  var forward = biconds.filter(bc=>!truths.filter(exp=>equiv(IF(bc.lhs,bc.rhs),exp)).length);  // Without the forward
  var backward = biconds.filter(bc=>!truths.filter(exp=>equiv(IF(bc.rhs,bc.lhs),exp)).length); // Or backward conditionals written
  for(let bc of forward){
    steps.push({type:'derived', reason:'BC',exp:IF(bc.lhs,bc.rhs),from:[bc]});
  }
  for(let bc of backward){
    steps.push({type:'derived', reason:'BC',exp:IF(bc.rhs,bc.lhs),from:[bc]});
  }
  
  // Use simplification to add new truths to use
  var ands  = truths.filter(exp=>exp.type === 'binary' && exp.connective === '^');// Find conjuctions
  var left  = ands.filter(and=>!truths.filter(exp=>equiv(and.lhs,exp)).length);   // Without the left
  var right = ands.filter(and=>!truths.filter(exp=>equiv(and.rhs,exp)).length);   // Or right expressions written
  for(let and of left){
    steps.push({type:'derived', reason:'S',exp:and.lhs,from:[and]});
  }
  for(let and of right){
    steps.push({type:'derived', reason:'S',exp:and.rhs,from:[and]});
  }
  
  // Use Modus Tollendo Ponens to add new truths
  var ors  = truths.filter(exp=>exp.type === 'binary' && exp.connective === 'v');                                           // Find disjuctions
  left  = ors.filter(or=>!truths.filter(exp=>equiv(or.lhs,exp)).length && truths.filter(exp=>contra(or.rhs,exp)).length);   // Without the left and a negation of the right
  right = ors.filter(or=>!truths.filter(exp=>equiv(or.rhs,exp)).length && truths.filter(exp=>contra(or.lhs,exp)).length);   // Or without the right and a negation of the left
  for(let or of left){
    for(let exp of truths){
      if(contra(exp,or.rhs)){
        steps.push(...reduction(exp,NOT(or.rhs)));
        break;
      }
    }
    steps.push({type: 'derived', reason:'MTP',exp:or.lhs,from:[NOT(or.rhs),or]});
  }
  for(let or of right){
    for(let exp of truths){
      if(contra(exp,or.lhs)){
        steps.push(...reduction(exp,NOT(or.lhs)));
        break;
      }
    }
    steps.push({type: 'derived', reason:'MTP',exp:or.rhs,from:[NOT(or.lhs),or]});
  }
  
  
  return [steps,steps.map(a=>a.exp)];
}

// Uses Double negatition to reduce expressions
function reduction(from, to){
  var from_ = simplify(from);
  var to_ = simplify(to);
  var steps = [];
  if(to_.i > from_.i){
    for(let i = 0; i < (to_.i-from_.i)/2; i++){
      steps.push({type:'derived', reason:'DN',exp:NOT(NOT(from)),from:[from]});
      from = NOT(NOT(from));
    }
  }else{
    for(let i = 0; i < (from_.i-to_.i)/2; i++){
      steps.push({type:'derived', reason:'DN',exp:to,from:[NOT(NOT(to))]});
      to = NOT(NOT(to));
    }
    steps = steps.reverse();
  }
  return steps
}