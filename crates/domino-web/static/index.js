const dominoWorker = new Worker("domino-worker.js", {type: "module"});
const dominoOutput = document.getElementById("domino_output");
const dominoOutputTemplate = document.getElementById("domino_output_template");
const logOutput = document.getElementById("log_output");

dominoWorker.onmessage = (e) => {
    console.log(e.data);
    console.log(e.data.func);
    switch (e.data.func) {
    case "proofsteps": {
        const clone = document.importNode(dominoOutputTemplate.content, true);
        clone.querySelector("h5").innerHTML = `${e.data.func} (${e.data.filename})`;
        clone.querySelector("pre").innerHTML = e.data.data;
        dominoOutput.appendChild(clone);
        break;
    }
    case "cvc-solve": {
        const clone = document.importNode(dominoOutputTemplate.content, true);
        clone.querySelector("h5").innerHTML = `${e.data.func}`;
        clone.querySelector("pre").innerHTML = e.data.data;
        dominoOutput.appendChild(clone);
        break;
    }
    case "domino-ui": {
        const clone = document.importNode(dominoOutputTemplate.content, true);
        clone.querySelector("h5").innerHTML = `${e.data.func}`;
        clone.querySelector("pre").innerHTML = "";
        dominoOutput.appendChild(clone);
        break;
    }
    case "log": {
        const elem = document.createElement("p");
        pelem.innerHTML = e.data;
        logOutput.appendChild(elem);
        break;
    }
    }
}

dominoWorker.onerror = (error) => {
    console.log(error.message);
    console.log(error);
}
console.log(dominoWorker);

let proofstep_button = document.getElementById("button_proof_steps");
proofstep_button.addEventListener("click", function() {
    let zipfile = document.getElementById("file_upload").files[0];
    console.log(zipfile);
    zipfile.arrayBuffer().then(function (bs) {
        dominoWorker.postMessage({func: 'proofsteps', data: new Uint8Array(bs), filename: zipfile.name})
    });
});

let cvctest_button = document.getElementById("button_cvctest");
cvctest_button.addEventListener("click", function() {
    dominoWorker.postMessage({func: 'cvctest'})
});

let prove_button = document.getElementById("button_prove");
prove_button.addEventListener("click", function() {
    let zipfile = document.getElementById("file_upload").files[0];
    console.log(zipfile);
    zipfile.bytes().then(function (bs) {
        let output_element = document.getElementById("domino_output_element");
        dominoWorker.postMessage({func: 'prove', data: bs, filename: zipfile.name})
    });
});

let check_sat_button = document.getElementById("button_check_sat");
check_sat_button.addEventListener("click", function() {
    const smt = document.getElementById("cvc_input_element").value;
    dominoWorker.postMessage({func: 'check-sat', data: smt})
});

let check_get_model = document.getElementById("button_get_model");
check_get_model.addEventListener("click", function() {
    const smt = document.getElementById("cvc_input_element").value;
    dominoWorker.postMessage({func: 'get-model', data: smt})
});        
