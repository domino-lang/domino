import init, { load, proofsteps, prove, 
               list_packages, list_games, list_theorems } from './domino/domino_web.js';
import {CVC, Solver, get_cvc} from "./cvc.js";


let files_collection = new Map();

onmessage = (e) => {
    console.log(e.data.func, e.data);
    switch(e.data.func) {
    case "load": {
        let files = load(e.data.data);
        files_collection.set(e.data.project, files);
        postMessage({
            func: "load",
            filename: e.data.filename,
            project: e.data.project,
        });
        break;
    }
    case "proofsteps": {
        let files = files_collection.get(e.data.project);
        proofsteps(e.data.project, files);
        break
    }
    case "prove": {
        let files = files_collection.get(e.data.project);
        prove(e.data.project, files, e.data.theorem);
        break
    }
    case "list-packages": {
        let files = files_collection.get(e.data.project);
        let result = list_packages(files);
        postMessage({
            func: "list-packages",
            data: result,
            project: e.data.project,
        });
        break
    }
    case "list-games": {
        let files = files_collection.get(e.data.project);
        let result = list_games(files);
        postMessage({
            func: "list-games",
            data: result,
            project: e.data.project,
        });
        break
    }
    case "list-theorems": {
        let files = files_collection.get(e.data.project);
        let result = list_theorems(files);
        postMessage({
            func: "list-theorems",
            data: result,
            project: e.data.project,
        });
        break
    }


    case "cvctest": {
        const solver = new Solver(get_cvc());
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
        const solver = new Solver(get_cvc());
        solver.add_smt(e.data.data);
        postMessage({func: "cvc-solve", data: solver.check_sat()});
        break;
    }
    case "get-model":
        const solver = new Solver(get_cvc());
        solver.add_smt(e.data.data);
        postMessage({func: "cvc-solve", data: solver.check_sat()});
        postMessage({func: "cvc-solve", data: solver.get_model()});
        break;
    }
}


async function init_domino() {
    await init()
}

init_domino();

