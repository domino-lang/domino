


## Building Everything

To build domino and automatically place it in the correct location, run

```
wasm-pack build --target web -d static/domino/  crates/domino-web/
```

Build CVC:

```
WASM_FLAGS:STRING=-s EXPORTED_FUNCTIONS=_main,_cvc5_parser_new,_cvc5_parser_set_inc_str_input,_cvc5_parser_append_inc_str_input,_cvc5_parser_next_command,_cvc5_new,_cvc5_cmd_invoke,_cvc5_symbol_manager_new,_cvc5_term_manager_new,_cvc5_term_manager_new,_cvc5_parser_done,_cvc5_check_sat,_cvc5_get_model,_cvc5_result_to_string,_cvc5_result_is_sat,_cvc5_result_is_unsat,_cvc5_result_is_unknown,_cvc5_result_release,_malloc,_free -s MODULARIZE=1 -s EXPORT_NAME=Cvc5Module -s ALLOW_MEMORY_GROWTH=1 -s NO_EXIT_RUNTIME=1 -s INVOKE_RUN=0 -s EXPORT_ES6=1 -s ENVIRONMENT=web,worker -s EXPORTED_RUNTIME_METHODS=callMain,FS,run,UTF8ToString,cwrap,ccall,setValue,getValue
```

Run locally e.g. via: 

```
python3 -m http.server -d crates/domino-web/static
```
