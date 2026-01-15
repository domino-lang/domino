const dominoWorker = new Worker("domino-worker.js", {type: "module"});
const dominoOutput = document.getElementById("domino_output");
const dominoOutputTemplate = document.getElementById("domino_output_template");
const proofUITemplate = document.getElementById("proof_ui_template");
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
    case "domino-test": {
        const clone = document.importNode(dominoOutputTemplate.content, true);
        clone.querySelector("h5").innerHTML = `${e.data.func}`;
        clone.querySelector("pre").innerHTML = e.data.data;
        dominoOutput.appendChild(clone);
        break;
    }
    case "domino-ui": 
        document.current_proof_ui.handle_msg(e.data);
        break;
    case "log": {
        const elem = document.createElement("p");
        pelem.innerHTML = e.data;
        logOutput.appendChild(elem);
        break;
    }
    }
}


class ProofUI {
    constructor(filename) {
        const clone = document.importNode(proofUITemplate.content, true)
        this.root_element = dominoOutput.appendChild(clone.children[0]);
        const h3 = document.createElement("h3");
        h3.innerHTML = filename;
        this.root_element.insertBefore(h3, this.root_element.children[0]);
    }

    start_theorem(msg) {
        const template = document.getElementById("template_ui_theorem");
        const clone = document.importNode(template.content, true);
        clone.querySelector("h4").innerHTML = `Theorem: ${msg["theorem-name"]}`;
        this.current_theorem = this.root_element.appendChild(clone.children[0]);
    }

    start_proofstep(msg) {
        const template = document.getElementById("template_ui_proofstep");
        const clone = document.importNode(template.content, true);
        clone.querySelector("h5").innerHTML = `Proofstep: ${msg["proofstep-name"]}`;
        this.current_proofstep = this.current_theorem.appendChild(clone.children[0]);
    }

    start_oracle(msg) {
        const template = document.getElementById("template_ui_oracle");
        const clone = document.importNode(template.content, true);
        clone.querySelector("h6").innerHTML = `Oracle: ${msg["oracle"]}`;
        this.current_oracle = this.current_proofstep.appendChild(clone.children[0]);
        this.current_lemma_count = msg.lemmata;
    }

    start_lemma(msg) {
        const elem = document.createElement("div");
        elem.style.backgroundColor = "#aaa";
        const width = 95n / this.current_lemma_count;
        elem.style.width = `${width}%`;
        elem.style.display = "inline-block";
        elem.style.margin = "0 auto";
        elem.innerHTML = msg.lemma;
        this.current_lemma = this.current_oracle.querySelector(".ui-lemmata").appendChild(elem);
    }

    finish_lemma(msg) {
        this.current_lemma.style.backgroundColor = "#1b1";
    }

    finish_oracle(msg) {
        this.current_oracle.style.backgroundColor = "#1c1";
    }

    finish_proofstep(msg) {
        this.current_proofstep.style.backgroundColor = "#1d1";
    }

    finish_theorem(msg) {
        this.current_theorem.style.backgroundColor = "#1e1";
    }

    handle_msg(msg) {
        console.log("ProofUI", msg);
        switch (msg.stage) {
        case "start-theorem":
            this.start_theorem(msg);
            break;
        case "start-proofstep":
            this.start_proofstep(msg);
            break;
        case "start-oracle":
            this.start_oracle(msg);
            break;
        case "start-lemma":
            this.start_lemma(msg);
            break;
        case "finish-lemma":
            this.finish_lemma(msg);
            break;
        case "finish-oracle":
            this.finish_oracle(msg);
            break;
        case "finish-proofstep":
            this.finish_proofstep(msg);
            break;
        case "finish-theorem":
            this.finish_theorem(msg);
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

let dominotest_button = document.getElementById("button_dominotest");
dominotest_button.addEventListener("click", function() {
    dominoWorker.postMessage({func: 'dominotest'})
});

let prove_button = document.getElementById("button_prove");
prove_button.addEventListener("click", function() {
    let zipfile = document.getElementById("file_upload").files[0];
    console.log(zipfile);
    zipfile.arrayBuffer().then(function (bs) {
        document.current_proof_ui = new ProofUI(zipfile.name);
        let output_element = document.getElementById("domino_output_element");
        dominoWorker.postMessage({func: 'prove', data: new Uint8Array(bs), filename: zipfile.name})
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
