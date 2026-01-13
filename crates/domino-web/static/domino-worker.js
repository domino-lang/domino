import init, { helloworld, proofsteps, prove, test } from './pkg/domino_web.js';
import Cvc5Module from "./cvc5/cvc5.js";
import {CVC, Solver} from "./cvc.js";


let cvc;

onmessage = (e) => {
    console.log(e.data.func, e.data);
    switch(e.data.func) {
    case "proofsteps":
        console.log("proofsteps");
        postMessage({func: "proofsteps", data: proofsteps(e.data.data), filename: e.data.filename});
        break
    case "cvctest": {
        const solver = new Solver(cvc);
        solver.add_smt("(declare-const foo Int)");
        solver.add_smt("(declare-const bar Int)");
        console.log(solver.check_sat());
        postMessage({func: "cvc-solve", data: solver.get_model()});
        solver.add_smt("(assert (< foo bar))");
        console.log(solver.check_sat());
        postMessage({func: "cvc-solve", data: solver.get_model()});
        break;
    }
    case "dominotest":
        postMessage({func: "domino-test", data: test(cvc)});
        break;
    case "check-sat": {
        const solver = new Solver(cvc);
        solver.add_smt(e.data.data);
        postMessage({func: "cvc-solve", data: solver.check_sat()});
        break;
    }
    case "get-model":
        const solver = new Solver(cvc);
        solver.add_smt(e.data.data);
        postMessage({func: "cvc-solve", data: solver.check_sat()});
        postMessage({func: "cvc-solve", data: solver.get_model()});
        break;
    case "prove":
        console.log("prove start");
        prove(e.data.data);
        console.log("prove end");
        break;
    }
}



Cvc5Module({
    locateFile: function(fname) {
        return `cvc5/${fname}`;
    },
    print: function(text) {
        postMessage({func: "cvc-solve", data: text});
    },

}).then(instance => {cvc = new CVC(instance)});

async function init_domino() {
    await init()
}

init_domino();

