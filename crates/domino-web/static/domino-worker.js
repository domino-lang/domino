import init, { helloworld, proofsteps, prove } from './pkg/domino_web.js';
import Cvc5Module from "./cvc5/cvc5.js";



class Solver {
    constructor(cvc) {
        this.cvc = cvc;
        this.tm = cvc._term_manager_new();
        this.solver = cvc._new(this.tm);
        this.sm = cvc._symbol_manager_new(this.tm);
        this.parser = cvc._parser_new(this.solver, this.sm);
        cvc._parser_set_inc_str_input(this.parser, 0, "domino");
        this.add_smt('(set-logic ALL)');
        this.add_smt('(set-option :produce-models true)');
        this.add_smt('(set-option :incremental true)');
    }

    add_smt(smt) {
        const cvc = this.cvc;
        cvc._parser_append_inc_str_input(this.parser, smt);
    }

    check_sat() {
        const cvc = this.cvc;
        const err = cvc._malloc(4);
        while (! cvc._parser_done(this.parser)) {
            cvc._set_value(err, 0, 'i32');
            const cmd = cvc._parser_next_command(this.parser, err);
            const errval = cvc._get_value(err, 'i32');
            if (errval) {
                msg = cvc._utf8_to_string(errval);
                console.error(msg);
                cvc._free(err);
                break;
            }
            if (cmd == 0) break;
            const out = cvc._cmd_invoke(cmd, this.solver, this.sm);
            console.log(out);
        }
        const result = cvc._check_sat(this.solver);
        const ret = cvc._result_to_string(result);
        cvc._result_release(result);
        cvc._free(err);
        cvc._parser_set_inc_str_input(this.parser, 0, "domino");
        return ret;
    }

    get_model() {
        const cvc = this.cvc;
        const err = cvc._malloc(4);
        cvc._parser_append_inc_str_input(this.parser, "(get-model)")
        const cmd = cvc._parser_next_command(this.parser, err);
        const out = cvc._cmd_invoke(cmd, this.solver, this.sm);
        return out;
    }
}


class CVC {
    constructor(module) {
        this.module = module;

        this._term_manager_new = module.cwrap('cvc5_term_manager_new', 'number', []);
        this._new = module.cwrap('cvc5_new', 'number', ['number']);
        this._symbol_manager_new = module.cwrap('cvc5_symbol_manager_new', 'number', ['number']);
        this._parser_new = module.cwrap('cvc5_parser_new', 'number', ['number', 'number']);
        this._parser_set_inc_str_input = module.cwrap('cvc5_parser_set_inc_str_input', null, ['number', 'number', 'string']);
        this._parser_append_inc_str_input = module.cwrap('cvc5_parser_append_inc_str_input', null, ['number', 'string']);
        this._parser_next_command = module.cwrap('cvc5_parser_next_command', 'number', ['number', 'number']);
        this._parser_done = module.cwrap('cvc5_parser_done', 'number', ['number']);
        this._cmd_invoke = module.cwrap('cvc5_cmd_invoke', 'string', ['number', 'number', 'number']);
        this._check_sat = module.cwrap('cvc5_check_sat', 'number', ['number']);
        this._result_to_string = module.cwrap('cvc5_result_to_string', 'string', ['number']);
        this._result_is_sat = module.cwrap('cvc5_result_is_sat', 'number', ['number']);
        this._result_is_unsat = module.cwrap('cvc5_result_is_unsat', 'number', ['number']);
        this._result_is_unknown = module.cwrap('cvc5_result_is_unknown', 'number', ['number']);
        this._result_release = module.cwrap('cvc5_result_release', null, ['number']);

        this._malloc = module._malloc;
        this._free = module._free;
        this._set_value = module.setValue;
        this._get_value = module.getValue;
        this._utf8_to_string = module.UTF8ToString;
    }
}


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
