(* Prot_NoPrf: n = n, prf = func_prf, mac = func_mac *)

require import AllCore Distr FMap Int IntDiv Types.

module type Prot_NoPrf_Imports = {
  proc d_Eval(h : int, x : (int * int * bits_n * bits_n * bool)) : bits_n option
}.

module Prot_NoPrf (O : Prot_NoPrf_Imports) = {
  proc d_Run1(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : int;
    var acc : bool option;
    var ni_ : bits_n option;
    var nr : bits_n option;
    var kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var ni : bits_n;
    ec_result <- None;
    (d_U, u, d_V, ltk, acc, ni_, nr, kmac, sid, mess) <- state;
    if (u = false) {
      if (acc = None) {
        if (mess = 0) {
          ni <$ dbits_n;
          ec_result <- Some ((d_U, u, d_V, ltk, None, Some ni, nr, kmac, sid, 1), ni);
        }
      }
    }
    return ec_result;
  }

  proc d_Run2(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), ni : bits_n) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    var d_U : int;
    var v : bool;
    var d_V : int;
    var ltk : int;
    var acc : bool option;
    var ni_ : bits_n option;
    var nr_ : bits_n option;
    var kmac_ : bits_n option;
    var sid_ : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var nr : bits_n;
    var ec_r1 : bits_n option;
    var kmac : bits_n;
    var tau : bits_n;
    var sid : (int * int * bits_n * bits_n * bits_n);
    ec_result <- None;
    (d_U, v, d_V, ltk, acc, ni_, nr_, kmac_, sid_, mess) <- state;
    if (v = true) {
      if (acc = None) {
        if (mess = 0) {
          nr <$ dbits_n;
          ec_r1 <@ O.d_Eval(ltk, (d_U, d_V, ni, nr, false));
          if (!(ec_r1 = None)) {
            kmac <- oget ec_r1;
            tau <- func_mac kmac nr 2;
            sid <- (d_U, d_V, ni, nr, tau);
            ec_result <- Some ((d_U, v, d_V, ltk, None, Some ni, Some nr, Some kmac, Some sid, 1), (nr, tau));
          }
        }
      }
    }
    return ec_result;
  }

  proc d_Run3(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : int;
    var acc : bool option;
    var ni : bits_n option;
    var nr_ : bits_n option;
    var kmac_ : bits_n option;
    var sid_ : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var nr : bits_n;
    var tau : bits_n;
    var unwrap_1 : bits_n;
    var ec_r1 : bits_n option;
    var kmac : bits_n;
    var unwrap_2 : bits_n;
    var tau_ : bits_n;
    var unwrap_3 : bits_n;
    var sid : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : bits_n;
    ec_result <- None;
    (d_U, u, d_V, ltk, acc, ni, nr_, kmac_, sid_, mess) <- state;
    if (u = false) {
      if (acc = None) {
        if (mess = 1) {
          (nr, tau) <- msg;
          if (!(ni = None)) {
            unwrap_1 <- oget ni;
            ec_r1 <@ O.d_Eval(ltk, (d_U, d_V, unwrap_1, nr, false));
            if (!(ec_r1 = None)) {
              kmac <- oget ec_r1;
              if (!(ni = None)) {
                unwrap_2 <- oget ni;
                tau_ <- func_mac kmac unwrap_2 3;
                if (!(ni = None)) {
                  unwrap_3 <- oget ni;
                  sid <- (d_U, d_V, unwrap_3, nr, tau);
                  if (func_mac kmac nr 2 = tau) {
                    if (!(ni = None)) {
                      unwrap_4 <- oget ni;
                      ec_result <- Some ((d_U, u, d_V, ltk, None, ni, Some nr, Some kmac, Some sid, 2), (unwrap_4, tau_));
                    }
                  } else {
                    ec_result <- Some (state, (zero_n, zero_n));
                  }
                }
              }
            }
          }
        }
      }
    }
    return ec_result;
  }

  proc d_Run4(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    var d_U : int;
    var v : bool;
    var d_V : int;
    var ltk : int;
    var acc : bool option;
    var ni_ : bits_n option;
    var nr : bits_n option;
    var kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var ni : bits_n;
    var tau : bits_n;
    var unwrap_1 : bits_n;
    var unwrap_2 : bits_n;
    var unwrap_3 : bits_n;
    var tau_ : bits_n;
    ec_result <- None;
    (d_U, v, d_V, ltk, acc, ni_, nr, kmac, sid, mess) <- state;
    if (v = true) {
      if (acc = None) {
        if (mess = 1) {
          (ni, tau) <- msg;
          if (!(kmac = None)) {
            unwrap_1 <- oget kmac;
            if (!(ni_ = None)) {
              unwrap_2 <- oget ni_;
              if (func_mac unwrap_1 ni 3 = tau /\ ni = unwrap_2) {
                acc <- Some true;
                if (!(kmac = None)) {
                  unwrap_3 <- oget kmac;
                  tau_ <- func_mac unwrap_3 zero_n 4;
                  ec_result <- Some ((d_U, v, d_V, ltk, acc, ni_, nr, kmac, sid, 2), tau_);
                }
              } else {
                acc <- Some false;
                ec_result <- Some ((d_U, v, d_V, ltk, acc, ni_, nr, kmac, sid, 2), zero_n);
              }
            }
          }
        }
      }
    }
    return ec_result;
  }

  proc d_Run5(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), tau : bits_n) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option;
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : int;
    var acc : bool option;
    var ni : bits_n option;
    var nr : bits_n option;
    var kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var unwrap_1 : bits_n;
    ec_result <- None;
    (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- state;
    if (u = false) {
      if (acc = None) {
        if (mess = 2) {
          if (!(kmac = None)) {
            unwrap_1 <- oget kmac;
            if (func_mac unwrap_1 zero_n 4 = tau) {
              ec_result <- Some ((d_U, u, d_V, ltk, Some true, ni, nr, kmac, sid, 3), true);
            } else {
              ec_result <- Some (state, false);
            }
          }
        }
      }
    }
    return ec_result;
  }
}.
