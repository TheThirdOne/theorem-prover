var input = document.getElementById("input");
var out = document.getElementById("output");

input.onkeydown = e=>{
  if(e.keyCode === 13){
    out.textContent = prettify(...writeProof(prove(pl(input.value))));
  }
};