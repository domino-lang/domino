(* Prot_NoKey: n = n, prf = func_prf, mac = func_mac *)

require import AllCore Distr FMap Int IntDiv Types.

module Prot_NoKey = {
  proc d_Run1(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option = {
    var ec_result : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : bits_n;
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

  proc d_Run2(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), ni : bits_n) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option = {
    var ec_result : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    var d_U : int;
    var v : bool;
    var d_V : int;
    var ltk : bits_n;
    var acc : bool option;
    var ni_ : bits_n option;
    var nr_ : bits_n option;
    var kmac_ : bits_n option;
    var sid_ : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var nr : bits_n;
    var kmac : bits_n;
    var tau : bits_n;
    var sid : (int * int * bits_n * bits_n * bits_n);
    ec_result <- None;
    (d_U, v, d_V, ltk, acc, ni_, nr_, kmac_, sid_, mess) <- state;
    if (v = true) {
      if (acc = None) {
        if (mess = 0) {
          nr <$ dbits_n;
          kmac <- func_prf ltk (d_U, d_V, ni, nr, false);
          tau <- func_mac kmac nr 2;
          sid <- (d_U, d_V, ni, nr, tau);
          ec_result <- Some ((d_U, v, d_V, ltk, None, Some ni, Some nr, Some kmac, Some sid, 1), (nr, tau));
        }
      }
    }
    return ec_result;
  }

  proc d_Run3(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option = {
    var ec_result : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : bits_n;
    var acc : bool option;
    var ni : bits_n option;
    var nr_ : bits_n option;
    var kmac_ : bits_n option;
    var sid_ : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var nr : bits_n;
    var tau : bits_n;
    var kmac : bits_n;
    var tau_ : bits_n;
    var sid : (int * int * bits_n * bits_n * bits_n);
    ec_result <- None;
    (d_U, u, d_V, ltk, acc, ni, nr_, kmac_, sid_, mess) <- state;
    if (u = false) {
      if (acc = None) {
        if (mess = 1) {
          (nr, tau) <- msg;
          if (!(ni = None)) {
            kmac <- func_prf ltk (d_U, d_V, oget ni, nr, false);
            tau_ <- func_mac kmac (oget ni) 3;
            sid <- (d_U, d_V, oget ni, nr, tau);
            if (func_mac kmac nr 2 = tau) {
              ec_result <- Some ((d_U, u, d_V, ltk, None, ni, Some nr, Some kmac, Some sid, 2), (oget ni, tau_));
            } else {
              ec_result <- Some (state, (zero_n, zero_n));
            }
          }
        }
      }
    }
    return ec_result;
  }

  proc d_Run4(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option = {
    var ec_result : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    var d_U : int;
    var v : bool;
    var d_V : int;
    var ltk : bits_n;
    var acc : bool option;
    var ni_ : bits_n option;
    var nr : bits_n option;
    var kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var ni : bits_n;
    var tau : bits_n;
    var tau_ : bits_n;
    ec_result <- None;
    (d_U, v, d_V, ltk, acc, ni_, nr, kmac, sid, mess) <- state;
    if (v = true) {
      if (acc = None) {
        if (mess = 1) {
          (ni, tau) <- msg;
          if (!(kmac = None)) {
            if (!(ni_ = None)) {
              if (func_mac (oget kmac) ni 3 = tau /\ ni = oget ni_) {
                acc <- Some true;
                tau_ <- func_mac (oget kmac) zero_n 4;
                ec_result <- Some ((d_U, v, d_V, ltk, acc, ni_, nr, kmac, sid, 2), tau_);
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

  proc d_Run5(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), tau : bits_n) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option = {
    var ec_result : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option;
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : bits_n;
    var acc : bool option;
    var ni : bits_n option;
    var nr : bits_n option;
    var kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    ec_result <- None;
    (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- state;
    if (u = false) {
      if (acc = None) {
        if (mess = 2) {
          if (!(kmac = None)) {
            if (func_mac (oget kmac) zero_n 4 = tau) {
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
