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
    var ec_result : int option <- None;
    var ltk_ : bits_n;
    kid_ <- kid_ + 1;
    if (ltk = None) {
      ltk_ <$ dbits_n;
      d_LTK.[kid_] <- ltk_;
      d_H.[kid_] <- true;
      ec_result <- Some kid_;
    } else {
      d_LTK <- if ltk = None then rem d_LTK kid_ else d_LTK.[kid_ <- oget ltk];
      d_H.[kid_] <- false;
      ec_result <- Some kid_;
    }
    return ec_result;
  }

  proc d_NewSession(d_U : int, u : bool, d_V : int, kid : int) : int option = {
    var ec_result : int option <- None;
    var unwrap_1 : bits_n;
    var ltk : bits_n;
    if (!(d_LTK.[kid] = None)) {
      ctr_ <- ctr_ + 1;
      if (d_LTK.[kid] = None) {

      } else {
        unwrap_1 <- oget d_LTK.[kid];
        ltk <- unwrap_1;
        d_State.[ctr_] <- (d_U, u, d_V, ltk, None, None, None, None, None, 0);
        d_Fresh <- if d_H.[kid] = None then rem d_Fresh ctr_ else d_Fresh.[ctr_ <- oget d_H.[kid]];
        ec_result <- Some ctr_;
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send1(ctr : int) : bits_n option = {
    var ec_result : bits_n option <- None;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg : bits_n;
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    if (!(d_State.[ctr] = None)) {
      if (d_State.[ctr] = None) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run1(state);
        if (ec_r1 = None) {

        } else {
          d_return <- oget ec_r1;
          (state, msg) <- d_return;
          d_State.[ctr] <- state;
          ec_result <- Some msg;
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send2(ctr : int, msg : bits_n) : (bits_n * bits_n) option = {
    var ec_result : (bits_n * bits_n) option <- None;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    if (!(d_State.[ctr] = None)) {
      if (d_State.[ctr] = None) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run2(state, msg);
        if (ec_r1 = None) {

        } else {
          d_return <- oget ec_r1;
          (state, msg_) <- d_return;
          d_State.[ctr] <- state;
          ec_result <- Some msg_;
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send3(ctr : int, msg : (bits_n * bits_n)) : (bits_n * bits_n) option = {
    var ec_result : (bits_n * bits_n) option <- None;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    if (!(d_State.[ctr] = None)) {
      if (d_State.[ctr] = None) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run3(state, msg);
        if (ec_r1 = None) {

        } else {
          d_return <- oget ec_r1;
          (state, msg_) <- d_return;
          d_State.[ctr] <- state;
          ec_result <- Some msg_;
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send4(ctr : int, msg : (bits_n * bits_n)) : bits_n option = {
    var ec_result : bits_n option <- None;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg_ : bits_n;
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    if (!(d_State.[ctr] = None)) {
      if (d_State.[ctr] = None) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run4(state, msg);
        if (ec_r1 = None) {

        } else {
          d_return <- oget ec_r1;
          (state, msg_) <- d_return;
          d_State.[ctr] <- state;
          ec_result <- Some msg_;
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send5(ctr : int, msg : bits_n) : bool option = {
    var ec_result : bool option <- None;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool);
    var stop : bool;
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option;
    if (!(d_State.[ctr] = None)) {
      if (d_State.[ctr] = None) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run5(state, msg);
        if (ec_r1 = None) {

        } else {
          d_return <- oget ec_r1;
          (state, stop) <- d_return;
          d_State.[ctr] <- state;
          ec_result <- Some stop;
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Reveal(ctr : int) : bits_n option = {
    var ec_result : bits_n option <- None;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
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
    var unwrap_2 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : bits_n;
    var unwrap_5 : bits_n;
    var k : bits_n;
    if (d_State.[ctr] = None) {

    } else {
      unwrap_1 <- oget d_State.[ctr];
      (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- unwrap_1;
      if (acc = Some true) {
        if (sid = None) {

        } else {
          unwrap_2 <- oget sid;
          if (d_RevTested.[unwrap_2] = None) {
            if (sid = None) {

            } else {
              unwrap_3 <- oget sid;
              d_RevTested.[unwrap_3] <- false;
              if (ni = None) {

              } else {
                unwrap_4 <- oget ni;
                if (nr = None) {

                } else {
                  unwrap_5 <- oget nr;
                  k <- func_prf ltk (d_U, d_V, unwrap_4, unwrap_5, true);
                  ec_result <- Some k;
                }
              }
            }
          } else {

          }
        }
      } else {

      }
    }
    return ec_result;
  }

  proc d_Test(ctr : int) : bits_n option = {
    var ec_result : bits_n option <- None;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
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
    var unwrap_2 : bool;
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : (int * int * bits_n * bits_n * bits_n);
    var k : bits_n;
    var unwrap_5 : bits_n;
    var unwrap_6 : bits_n;
    if (d_State.[ctr] = None) {

    } else {
      unwrap_1 <- oget d_State.[ctr];
      (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- unwrap_1;
      if (acc = Some true) {
        if (d_Fresh.[ctr] = None) {

        } else {
          unwrap_2 <- oget d_Fresh.[ctr];
          if (unwrap_2) {
            if (sid = None) {

            } else {
              unwrap_3 <- oget sid;
              if (d_RevTested.[unwrap_3] = None) {
                if (sid = None) {

                } else {
                  unwrap_4 <- oget sid;
                  d_RevTested.[unwrap_4] <- true;
                  if (b) {
                    k <$ dbits_n;
                    ec_result <- Some k;
                  } else {
                    if (ni = None) {

                    } else {
                      unwrap_5 <- oget ni;
                      if (nr = None) {

                      } else {
                        unwrap_6 <- oget nr;
                        k <- func_prf ltk (d_U, d_V, unwrap_5, unwrap_6, true);
                        ec_result <- Some k;
                      }
                    }
                  }
                }
              } else {

              }
            }
          } else {

          }
        }
      } else {

      }
    }
    return ec_result;
  }
}.
