(* KX_NoPrf: n = n *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces.

module KX_NoPrf (P_Prot : Interfaces.Prot_NoPrf_i) (P_Prf : Interfaces.M_PRF_i) = {
  var ctr_ : int
  var d_RevTested : ((int * int * bits_n * bits_n * bits_n), bool) fmap
  var d_Fresh : (int, bool) fmap
  var d_State : (int, (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)) fmap
  var b : bool

  proc init(b_ : bool) : unit = {
    ctr_ <- 0;
    d_RevTested <- empty;
    d_Fresh <- empty;
    d_State <- empty;
    b <- b_;
  }

  proc d_NewSession(d_U : int, u : bool, d_V : int, kid : int) : int option = {
    var ec_result : int option <- None<:int>;
    var hon : bool;
    var ec_r1 : bool option;
    ec_r1 <@ P_Prf.d_Hon(kid);
    if (ec_r1 = None<:bool>) {

    } else {
      hon <- oget ec_r1;
      d_State.[ctr_] <- (d_U, u, d_V, kid, None<:bool>, None<:bits_n>, None<:bits_n>, None<:bits_n>, None<:(int * int * bits_n * bits_n * bits_n)>, 0);
      d_Fresh.[ctr_] <- hon;
      ec_result <- Some ctr_;
    }
    return ec_result;
  }

  proc d_Send1(ctr : int) : bits_n option = {
    var ec_result : bits_n option <- None<:bits_n>;
    var unwrap_1 : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg : bits_n;
    var ec_r1 : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run1(state);
        if (ec_r1 = None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n)>) {

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
    var ec_result : (bits_n * bits_n) option <- None<:(bits_n * bits_n)>;
    var unwrap_1 : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    var ec_r1 : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run2(state, msg);
        if (ec_r1 = None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n))>) {

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
    var ec_result : (bits_n * bits_n) option <- None<:(bits_n * bits_n)>;
    var unwrap_1 : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    var ec_r1 : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run3(state, msg);
        if (ec_r1 = None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n))>) {

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
    var ec_result : bits_n option <- None<:bits_n>;
    var unwrap_1 : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg_ : bits_n;
    var ec_r1 : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run4(state, msg);
        if (ec_r1 = None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n)>) {

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
    var ec_result : bool option <- None<:bool>;
    var unwrap_1 : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool);
    var stop : bool;
    var ec_r1 : ((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run5(state, msg);
        if (ec_r1 = None<:((int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool)>) {

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
    var ec_result : bits_n option <- None<:bits_n>;
    var unwrap_1 : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
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
    var unwrap_2 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : bits_n;
    var unwrap_5 : bits_n;
    var k : bits_n;
    var ec_r1 : bits_n option;
    if (d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

    } else {
      unwrap_1 <- oget d_State.[ctr];
      (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- unwrap_1;
      if (acc = Some true) {
        if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

        } else {
          unwrap_2 <- oget sid;
          if (d_RevTested.[unwrap_2] = None<:bool>) {
            if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

            } else {
              unwrap_3 <- oget sid;
              d_RevTested.[unwrap_3] <- false;
              if (ni = None<:bits_n>) {

              } else {
                unwrap_4 <- oget ni;
                if (nr = None<:bits_n>) {

                } else {
                  unwrap_5 <- oget nr;
                  ec_r1 <@ P_Prf.d_Eval(ltk, (d_U, d_V, unwrap_4, unwrap_5, true));
                  if (ec_r1 = None<:bits_n>) {

                  } else {
                    k <- oget ec_r1;
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
    return ec_result;
  }

  proc d_Test(ctr : int) : bits_n option = {
    var ec_result : bits_n option <- None<:bits_n>;
    var unwrap_1 : (int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
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
    var unwrap_2 : bool;
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : (int * int * bits_n * bits_n * bits_n);
    var k : bits_n;
    var unwrap_5 : bits_n;
    var unwrap_6 : bits_n;
    var ec_r1 : bits_n option;
    if (d_State.[ctr] = None<:(int * bool * int * int * bool option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

    } else {
      unwrap_1 <- oget d_State.[ctr];
      (d_U, u, d_V, ltk, acc, ni, nr, kmac, sid, mess) <- unwrap_1;
      if (acc = Some true) {
        if (d_Fresh.[ctr] = None<:bool>) {

        } else {
          unwrap_2 <- oget d_Fresh.[ctr];
          if (unwrap_2) {
            if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

            } else {
              unwrap_3 <- oget sid;
              if (d_RevTested.[unwrap_3] = None<:bool>) {
                if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

                } else {
                  unwrap_4 <- oget sid;
                  d_RevTested.[unwrap_4] <- true;
                  if (b) {
                    k <$ dbits_n;
                    ec_result <- Some k;
                  } else {
                    if (ni = None<:bits_n>) {

                    } else {
                      unwrap_5 <- oget ni;
                      if (nr = None<:bits_n>) {

                      } else {
                        unwrap_6 <- oget nr;
                        ec_r1 <@ P_Prf.d_Eval(ltk, (d_U, d_V, unwrap_5, unwrap_6, true));
                        if (ec_r1 = None<:bits_n>) {

                        } else {
                          k <- oget ec_r1;
                          ec_result <- Some k;
                        }
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
