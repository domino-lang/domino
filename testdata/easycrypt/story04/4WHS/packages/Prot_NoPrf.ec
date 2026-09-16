(* Prot_NoPrf: n = n, prf = func_prf, mac = func_mac *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces.

module Prot_NoPrf (P_Prf : Interfaces.M_PRF_i) = {
  proc d_Run1(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option <- None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n)>;
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
    (d_U, u, d_V, ltk, acc, ni_, nr, kmac, sid, mess) <- state;
    if (u = false) {
      if (acc = None<:bool>) {
        if (mess = 0) {
          ni <$ dbits_n;
          ec_result <- Some ((d_U, u, d_V, ltk, None<:bool>, Some ni, nr, kmac, sid, 1), ni);
        } else {

        }
      } else {

      }
    } else {

    }
    return ec_result;
  }

  proc d_Run2(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), ni : bits_n) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option <- None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n))>;
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
    var kmac : bits_n;
    var tau : bits_n;
    var sid : (int * int * bits_n * bits_n * bits_n);
    var ec_r1 : bits_n option;
    (d_U, v, d_V, ltk, acc, ni_, nr_, kmac_, sid_, mess) <- state;
    if (v = true) {
      if (acc = None<:bool>) {
        if (mess = 0) {
          ec_r1 <@ P_Prf.d_Eval(ltk, (d_U, d_V, ni, nr, false));
          if (ec_r1 = None<:bits_n>) {

          } else {
            kmac <- oget ec_r1;
            tau <- func_mac kmac nr 2;
            sid <- (d_U, d_V, ni, nr, tau);
            ec_result <- Some ((d_U, v, d_V, ltk, None<:bool>, Some ni, Some nr, Some kmac, Some sid, 1), (nr, tau));
          }
        } else {

        }
      } else {

      }
    } else {

    }
    return ec_result;
  }

  proc d_Run3(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option <- None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n))>;
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
    var kmac : bits_n;
    var unwrap_2 : bits_n;
    var tau_ : bits_n;
    var unwrap_3 : bits_n;
    var sid : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : bits_n;
    var ec_r1 : bits_n option;
    (d_U, u, d_V, ltk, acc, ni, nr_, kmac_, sid_, mess) <- state;
    if (u = false) {
      if (acc = None<:bool>) {
        if (mess = 1) {
          (nr, tau) <- msg;
          if (ni = None<:bits_n>) {

          } else {
            unwrap_1 <- oget ni;
            ec_r1 <@ P_Prf.d_Eval(ltk, (d_U, d_V, unwrap_1, nr, false));
            if (ec_r1 = None<:bits_n>) {

            } else {
              kmac <- oget ec_r1;
              if (ni = None<:bits_n>) {

              } else {
                unwrap_2 <- oget ni;
                tau_ <- func_mac kmac unwrap_2 3;
                if (ni = None<:bits_n>) {

                } else {
                  unwrap_3 <- oget ni;
                  sid <- (d_U, d_V, unwrap_3, nr, tau);
                  if (func_mac kmac nr 2 = tau) {
                    if (ni = None<:bits_n>) {

                    } else {
                      unwrap_4 <- oget ni;
                      ec_result <- Some ((d_U, u, d_V, ltk, None<:bool>, ni, Some nr, Some kmac, Some sid, 2), (unwrap_4, tau_));
                    }
                  } else {
                    ec_result <- Some (state, (zero_n, zero_n));
                  }
                }
              }
            }
          }
        } else {

        }
      } else {

      }
    } else {

    }
    return ec_result;
  }

  proc d_Run4(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option <- None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n)>;
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
    (d_U, v, d_V, ltk, acc, ni_, nr, kmac, sid, mess) <- state;
    if (v = true) {
      if (acc = None<:bool>) {
        if (mess = 1) {
          (ni, tau) <- msg;
          if (kmac = None<:bits_n>) {

          } else {
            unwrap_1 <- oget kmac;
            if (ni_ = None<:bits_n>) {

            } else {
              unwrap_2 <- oget ni_;
              if (func_mac unwrap_1 ni 3 = tau /\ ni = unwrap_2) {
                acc <- Some true;
                if (kmac = None<:bits_n>) {

                } else {
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
        } else {

        }
      } else {

      }
    } else {

    }
    return ec_result;
  }

  proc d_Run5(state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), tau : bits_n) : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option = {
    var ec_result : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option <- None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool)>;
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
    (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- state;
    if (u = false) {
      if (acc = None<:bool>) {
        if (mess = 2) {
          if (kmac = None<:bits_n>) {

          } else {
            unwrap_1 <- oget kmac;
            if (func_mac unwrap_1 zero_n 4 = tau) {
              ec_result <- Some ((d_U, u, d_V, ltk, Some true, ni, nr, kmac, sid, 3), true);
            } else {
              ec_result <- Some (state, false);
            }
          }
        } else {

        }
      } else {

      }
    } else {

    }
    return ec_result;
  }
}.
