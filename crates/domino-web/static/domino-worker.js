import init, { helloworld, proofsteps, prove } from './pkg/domino_web.js';

async function init_domino() {
    await init()
}

init_domino();

onmessage = (e) => {
    console.log(e.data.func, e.data);
    switch(e.data.func) {
    case "proofsteps":
        console.log("proofsteps");
        postMessage({func: "proofsteps", data: proofsteps(e.data.data), filename: e.data.filename});
        break;
    case "prove":
        console.log("prove start");
        prove(e.data.data);
        console.log("prove end");
        break;
    }
}


const cvcWorker = new Worker("cvc-worker.js");
cvcWorker.onmessage = (e) => {
    console.log(e);
    postMessage(e.data);
}
cvcWorker.postMessage("(set-logic ALL)(declare-const test Int)(check-sat)(get-model)")


          // proofstep_button.addEventListener("click", function() {
          //     let zipfile = document.getElementById("file_upload").files[0];
          //     console.log(zipfile);
          //     zipfile.bytes().then(function (bs) {
          //         let output_element = document.getElementById("domino_output_element");
          //         output_element.innerHTML = proofsteps(bs);
          //     });
          // });


