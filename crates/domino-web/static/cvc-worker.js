var Module = {
    arguments: ["--no-interactive", "--lang=smt2", "--incremental", "--produce-models", "--arrays-exp", "input.smt2"],
    print: function(text) {
        postMessage({func: "cvc-solve", data: text});
    },
    locateFile: function(fname) {
        return `cvc5/${fname}`;
    }
};

importScripts("cvc5/cvc5.max.js");

onmessage = (e) => {
    console.log(e);
    Module.preRun = function() {
        Module.FS.writeFile('input.smt2', e.data);
    }
    shouldRunNow = true;
    run();
}




          // stdin: function() {
          //     console.log(i);
          //     if (i % 3 == 0) {
          //         let input_element = document.getElementById("cvc_input_element");
          //         let text = input_element.value;
          //         if (i/3 < text.length) {
          //             i = i+1;
          //             return text.charCodeAt(i/3);
          //         } else {
          //             return null;
          //         }
          //     } else {
          //         i = i+1;
          //         return null;
          //     }
          // },
