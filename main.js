var input = document.getElementById("input");
var out = document.getElementById("output");

input.onkeydown = e=>{
  
  if(e.keyCode === 13){
    var exp = pl(input.value);
    var wrong = findWrong(exp);
    if(!wrong){
      out.textContent = prettify(...writeProof(prove(exp)));
    }else{
      out.textContent = 'Not a tautology, the variable binding:\n'+ [...wrong.keys()].map(key=>''+key+': '+wrong.get(key)).join('\n')+'\n disproves it.';
    }
  }
};