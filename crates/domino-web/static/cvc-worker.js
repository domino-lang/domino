
console.log(cvc_module);

onmessage = (e) => {
    console.log(12);
    console.log(e.data);
    console.log(cvc_module);
    cvc_module.preRun = function() {
        cvc_module.FS.writeFile('input.smt2', e.data);
    }
    shouldRunNow = true;
    cvc_module._main();
}




//console.log(Module);


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
