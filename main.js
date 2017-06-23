var input = document.getElementById("input");
var out = document.getElementById("output");

input.onkeydown = ()=>{
  setTimeout(process,0);
};

var process = ()=>{
  var exp = flexibleParse(lex(input.value));
  if(str(exp) !== input.value){
    out.textContent = input.value + ' is not a formally valid formula, interpretting as ' + str(exp) + '\n';
  }else{
    out.textContent = '';
  }
  var wrong = findWrong(exp);
  if(!wrong){
    out.textContent += prettify(...writeProof(pruneSteps(prove(exp))));
  }else{
    out.textContent += 'Not a tautology, the variable binding:\n'+ [...wrong.keys()].map(key=>''+key+': '+wrong.get(key)).join('\n')+'\n disproves it.';
  }
};