(* KX_NoKeys: n = n, prf = func_prf *)

require import AllCore Distr FMap Int IntDiv Types.

module type KX_NoKeys_Imports = {
  proc d_Run1(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option
  proc d_Run2(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), ni : bits_n) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option
  proc d_Run3(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option
  proc d_Run4(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), msg : (bits_n * bits_n)) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option
  proc d_Run5(state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int), tau : bits_n) : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option
}.

module KX_NoKeys (O : KX_NoKeys_Imports) = {
  var d_LTK : (int, bits_n) fmap
  var d_H : (int, bool) fmap
  var ctr_ : int
  var kid_ : int
  var d_RevTested : ((int * int * bits_n * bits_n * bits_n), bool) fmap
  var d_Fresh : (int, bool) fmap
  var d_State : (int, (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)) fmap
  var b : bool

  proc init(b_ : bool) : unit = {
    d_LTK <- empty;
    d_H <- empty;
    ctr_ <- 0;
    kid_ <- 0;
    d_RevTested <- empty;
    d_Fresh <- empty;
    d_State <- empty;
    b <- b_;
  }

  proc d_NewKey(ltk : bits_n option) : int option = {
    var ec_result : int option;
    var ltk_ : bits_n;
    ec_result <- None;
    kid_ <- kid_ + 1;
    if (ltk = None) {
      ltk_ <$ dbits_n;
      d_LTK.[kid_] <- ltk_;
      d_H.[kid_] <- true;
    } else {
      d_LTK <- if ltk = None then rem d_LTK kid_ else d_LTK.[kid_ <- oget ltk];
      d_H.[kid_] <- false;
    }
    ec_result <- Some kid_;
    return ec_result;
  }

  proc d_NewSession(d_U : int, u : bool, d_V : int, kid : int) : int option = {
    var ec_result : int option;
    var ltk : bits_n;
    ec_result <- None;
    if (!(d_LTK.[kid] = None)) {
      ctr_ <- ctr_ + 1;
      ltk <- oget d_LTK.[kid];
      d_State.[ctr_] <- (d_U, u, d_V, ltk, None, None, None, None, None, 0);
      d_Fresh <- if d_H.[kid] = None then rem d_Fresh ctr_ else d_Fresh.[ctr_ <- oget d_H.[kid]];
      ec_result <- Some ctr_;
    }
    return ec_result;
  }

  proc d_Send1(ctr : int) : bits_n option = {
    var ec_result : bits_n option;
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg : bits_n;
    ec_result <- None;
    if (!(d_State.[ctr] = None)) {
      state <- oget d_State.[ctr];
      ec_r1 <@ O.d_Run1(state);
      if (!(ec_r1 = None)) {
        d_return <- oget ec_r1;
        (state, msg) <- d_return;
        d_State.[ctr] <- state;
        ec_result <- Some msg;
      }
    }
    return ec_result;
  }

  proc d_Send2(ctr : int, msg : bits_n) : (bits_n * bits_n) option = {
    var ec_result : (bits_n * bits_n) option;
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    ec_result <- None;
    if (!(d_State.[ctr] = None)) {
      state <- oget d_State.[ctr];
      ec_r1 <@ O.d_Run2(state, msg);
      if (!(ec_r1 = None)) {
        d_return <- oget ec_r1;
        (state, msg_) <- d_return;
        d_State.[ctr] <- state;
        ec_result <- Some msg_;
      }
    }
    return ec_result;
  }

  proc d_Send3(ctr : int, msg : (bits_n * bits_n)) : (bits_n * bits_n) option = {
    var ec_result : (bits_n * bits_n) option;
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    ec_result <- None;
    if (!(d_State.[ctr] = None)) {
      state <- oget d_State.[ctr];
      ec_r1 <@ O.d_Run3(state, msg);
      if (!(ec_r1 = None)) {
        d_return <- oget ec_r1;
        (state, msg_) <- d_return;
        d_State.[ctr] <- state;
        ec_result <- Some msg_;
      }
    }
    return ec_result;
  }

  proc d_Send4(ctr : int, msg : (bits_n * bits_n)) : bits_n option = {
    var ec_result : bits_n option;
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg_ : bits_n;
    ec_result <- None;
    if (!(d_State.[ctr] = None)) {
      state <- oget d_State.[ctr];
      ec_r1 <@ O.d_Run4(state, msg);
      if (!(ec_r1 = None)) {
        d_return <- oget ec_r1;
        (state, msg_) <- d_return;
        d_State.[ctr] <- state;
        ec_result <- Some msg_;
      }
    }
    return ec_result;
  }

  proc d_Send5(ctr : int, msg : bits_n) : bool option = {
    var ec_result : bool option;
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option;
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool);
    var stop : bool;
    ec_result <- None;
    if (!(d_State.[ctr] = None)) {
      state <- oget d_State.[ctr];
      ec_r1 <@ O.d_Run5(state, msg);
      if (!(ec_r1 = None)) {
        d_return <- oget ec_r1;
        (state, stop) <- d_return;
        d_State.[ctr] <- state;
        ec_result <- Some stop;
      }
    }
    return ec_result;
  }

  proc d_Reveal(ctr : int) : bits_n option = {
    var ec_result : bits_n option;
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
    var k : bits_n;
    ec_result <- None;
    if (!(d_State.[ctr] = None)) {
      (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- oget d_State.[ctr];
      if (acc = Some true) {
        if (!(sid = None)) {
          if (d_RevTested.[oget sid] = None) {
            d_RevTested.[oget sid] <- false;
            if (!(ni = None)) {
              if (!(nr = None)) {
                k <- func_prf ltk (d_U, d_V, oget ni, oget nr, true);
                ec_result <- Some k;
              }
            }
          }
        }
      }
    }
    return ec_result;
  }

  proc d_Test(ctr : int) : bits_n option = {
    var ec_result : bits_n option;
    var ec_done : bool;
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
    var k : bits_n;
    ec_result <- None;
    ec_done <- false;
    if (!(d_State.[ctr] = None)) {
      (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- oget d_State.[ctr];
      if (acc = Some true) {
        if (!(d_Fresh.[ctr] = None)) {
          if (oget d_Fresh.[ctr]) {
            if (!(sid = None)) {
              if (d_RevTested.[oget sid] = None) {
                d_RevTested.[oget sid] <- true;
                if (b) {
                  k <$ dbits_n;
                } else {
                  if (!(ni = None)) {
                    if (!(nr = None)) {
                      k <- func_prf ltk (d_U, d_V, oget ni, oget nr, true);
                    } else {
                      ec_done <- true;
                    }
                  } else {
                    ec_done <- true;
                  }
                }
                if (!ec_done) {
                  ec_result <- Some k;
                }
              }
            }
          }
        }
      }
    }
    return ec_result;
  }
}.
