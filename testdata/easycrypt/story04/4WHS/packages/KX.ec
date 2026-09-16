(* KX: n = n *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces.

module KX (P_Prot : Interfaces.Prot_i) = {
  var d_LTK : (int, bits_n) fmap
  var d_H : (int, bool) fmap
  var ctr_ : int
  var kid_ : int
  var d_RevTested : ((int * int * bits_n * bits_n * bits_n), bool) fmap
  var d_Fresh : (int, bool) fmap
  var d_First : ((int * int * bits_n * bits_n * bits_n), int) fmap
  var d_Second : ((int * int * bits_n * bits_n * bits_n), int) fmap
  var d_State : (int, (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)) fmap
  var b : bool

  proc init(b_ : bool) : unit = {
    d_LTK <- empty;
    d_H <- empty;
    ctr_ <- 0;
    kid_ <- 0;
    d_RevTested <- empty;
    d_Fresh <- empty;
    d_First <- empty;
    d_Second <- empty;
    d_State <- empty;
    b <- b_;
  }

  proc d_NewKey(ltk : bits_n option) : int option = {
    var ec_result : int option <- None<:int>;
    var ltk_ : bits_n;
    kid_ <- kid_ + 1;
    if (ltk = None<:bits_n>) {
      ltk_ <$ dbits_n;
      d_LTK.[kid_] <- ltk_;
      d_H.[kid_] <- true;
      ec_result <- Some kid_;
    } else {
      d_LTK <- if ltk = None<:bits_n> then rem d_LTK kid_ else d_LTK.[kid_ <- oget ltk];
      d_H.[kid_] <- false;
      ec_result <- Some kid_;
    }
    return ec_result;
  }

  proc d_NewSession(d_U : int, u : bool, d_V : int, kid : int) : int option = {
    var ec_result : int option <- None<:int>;
    var unwrap_1 : bits_n;
    var ltk : bits_n;
    if (!(d_LTK.[kid] = None<:bits_n>)) {
      ctr_ <- ctr_ + 1;
      if (d_LTK.[kid] = None<:bits_n>) {

      } else {
        unwrap_1 <- oget d_LTK.[kid];
        ltk <- unwrap_1;
        d_State.[ctr_] <- (d_U, u, d_V, ltk, None<:bool>, None<:bits_n>, None<:bits_n>, None<:bits_n>, None<:bits_n>, None<:(int * int * bits_n * bits_n * bits_n)>, 0);
        d_Fresh <- if d_H.[kid] = None<:bool> then rem d_Fresh ctr_ else d_Fresh.[ctr_ <- oget d_H.[kid]];
        ec_result <- Some ctr_;
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send1(ctr : int) : bits_n option = {
    var ec_result : bits_n option <- None<:bits_n>;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg : bits_n;
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run1(state);
        if (ec_r1 = None<:((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n)>) {

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
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run2(state, msg);
        if (ec_r1 = None<:((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n))>) {

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
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n));
    var msg_ : (bits_n * bits_n);
    var _U : int;
    var _u : bool;
    var _V : int;
    var _ltk : bits_n;
    var _acc : bool option;
    var _k : bits_n option;
    var _ni : bits_n option;
    var _nr : bits_n option;
    var _kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var _mess : int;
    var unwrap_2 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_5 : (int * int * bits_n * bits_n * bits_n);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n)) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run3(state, msg);
        if (ec_r1 = None<:((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * (bits_n * bits_n))>) {

        } else {
          d_return <- oget ec_r1;
          (state, msg_) <- d_return;
          (_U, _u, _V, _ltk, _acc, _k, _ni, _nr, _kmac, sid, _mess) <- state;
          if (_mess = 2) {
            if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

            } else {
              unwrap_2 <- oget sid;
              if (d_First.[unwrap_2] = None<:int>) {
                if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

                } else {
                  unwrap_3 <- oget sid;
                  d_First.[unwrap_3] <- ctr;
                  d_State.[ctr] <- state;
                  ec_result <- Some msg_;
                }
              } else {
                if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

                } else {
                  unwrap_4 <- oget sid;
                  if (d_Second.[unwrap_4] = None<:int>) {
                    if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

                    } else {
                      unwrap_5 <- oget sid;
                      d_Second.[unwrap_5] <- ctr;
                      d_State.[ctr] <- state;
                      ec_result <- Some msg_;
                    }
                  } else {
                    d_State.[ctr] <- state;
                    ec_result <- Some msg_;
                  }
                }
              }
            }
          } else {
            d_State.[ctr] <- state;
            ec_result <- Some msg_;
          }
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send4(ctr : int, msg : (bits_n * bits_n)) : bits_n option = {
    var ec_result : bits_n option <- None<:bits_n>;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n);
    var msg_ : bits_n;
    var _U : int;
    var _u : bool;
    var _V : int;
    var _ltk : bits_n;
    var acc : bool option;
    var _k : bits_n option;
    var _ni : bits_n option;
    var _nr : bits_n option;
    var _kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var _mess : int;
    var unwrap_2 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_5 : (int * int * bits_n * bits_n * bits_n);
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run4(state, msg);
        if (ec_r1 = None<:((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bits_n)>) {

        } else {
          d_return <- oget ec_r1;
          (state, msg_) <- d_return;
          d_State.[ctr] <- state;
          (_U, _u, _V, _ltk, acc, _k, _ni, _nr, _kmac, sid, _mess) <- state;
          if (acc = Some true) {
            if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

            } else {
              unwrap_2 <- oget sid;
              if (d_First.[unwrap_2] = None<:int>) {
                if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

                } else {
                  unwrap_3 <- oget sid;
                  d_First.[unwrap_3] <- ctr;
                  ec_result <- Some msg_;
                }
              } else {
                if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

                } else {
                  unwrap_4 <- oget sid;
                  if (d_Second.[unwrap_4] = None<:int>) {
                    if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

                    } else {
                      unwrap_5 <- oget sid;
                      d_Second.[unwrap_5] <- ctr;
                      ec_result <- Some msg_;
                    }
                  } else {
                    ec_result <- Some msg_;
                  }
                }
              }
            }
          } else {
            ec_result <- Some msg_;
          }
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Send5(ctr : int, msg : bits_n) : bool option = {
    var ec_result : bool option <- None<:bool>;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var state : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_return : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool);
    var stop : bool;
    var ec_r1 : ((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool) option;
    if (!(d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>)) {
      if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ P_Prot.d_Run5(state, msg);
        if (ec_r1 = None<:((int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int) * bool)>) {

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
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : bits_n;
    var acc : bool option;
    var k : bits_n option;
    var ni : bits_n option;
    var nr : bits_n option;
    var kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var unwrap_2 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : bits_n;
    if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

    } else {
      unwrap_1 <- oget d_State.[ctr];
      (d_U, u, d_V, ltk, acc, k, ni, nr, kmac, sid, mess) <- unwrap_1;
      if (acc = Some true) {
        if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

        } else {
          unwrap_2 <- oget sid;
          if (d_RevTested.[unwrap_2] = None<:bool>) {
            if (sid = None<:(int * int * bits_n * bits_n * bits_n)>) {

            } else {
              unwrap_3 <- oget sid;
              d_RevTested.[unwrap_3] <- false;
              if (k = None<:bits_n>) {

              } else {
                unwrap_4 <- oget k;
                ec_result <- Some unwrap_4;
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
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var d_U : int;
    var u : bool;
    var d_V : int;
    var ltk : bits_n;
    var acc : bool option;
    var k : bits_n option;
    var ni : bits_n option;
    var nr : bits_n option;
    var kmac : bits_n option;
    var sid : (int * int * bits_n * bits_n * bits_n) option;
    var mess : int;
    var unwrap_2 : bool;
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : (int * int * bits_n * bits_n * bits_n);
    var k_ : bits_n;
    var unwrap_5 : bits_n;
    if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

    } else {
      unwrap_1 <- oget d_State.[ctr];
      (d_U, u, d_V, ltk, acc, k, ni, nr, kmac, sid, mess) <- unwrap_1;
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
                    k_ <$ dbits_n;
                    ec_result <- Some k_;
                  } else {
                    if (k = None<:bits_n>) {

                    } else {
                      unwrap_5 <- oget k;
                      k_ <- unwrap_5;
                      ec_result <- Some k_;
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

  proc d_SameKey(ctr1 : int, ctr2 : int) : bool option = {
    var ec_result : bool option <- None<:bool>;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var _U : int;
    var _u : bool;
    var _V : int;
    var _ltk : bits_n;
    var acc1 : bool option;
    var k1 : bits_n option;
    var _ni : bits_n option;
    var _nr : bits_n option;
    var _kmac : bits_n option;
    var sid1 : (int * int * bits_n * bits_n * bits_n) option;
    var _mess : int;
    var unwrap_2 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var acc2 : bool option;
    var k2 : bits_n option;
    var sid2 : (int * int * bits_n * bits_n * bits_n) option;
    if (d_State.[ctr1] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

    } else {
      unwrap_1 <- oget d_State.[ctr1];
      (_U, _u, _V, _ltk, acc1, k1, _ni, _nr, _kmac, sid1, _mess) <- unwrap_1;
      if (d_State.[ctr2] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_2 <- oget d_State.[ctr2];
        (_U, _u, _V, _ltk, acc2, k2, _ni, _nr, _kmac, sid2, _mess) <- unwrap_2;
        if (b = false) {
          if (acc1 = acc2 /\ acc2 = Some true) {
            if (sid1 = sid2) {
              if (!(k1 = k2)) {
                ec_result <- Some true;
              } else {
                ec_result <- Some false;
              }
            } else {
              ec_result <- Some false;
            }
          } else {
            ec_result <- Some false;
          }
        } else {
          ec_result <- Some false;
        }
      }
    }
    return ec_result;
  }

  proc d_AtMost(ctr1 : int, ctr2 : int, ctr3 : int) : bool option = {
    var ec_result : bool option <- None<:bool>;
    var unwrap_1 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var _U : int;
    var _u : bool;
    var _V : int;
    var _ltk : bits_n;
    var acc1 : bool option;
    var _k : bits_n option;
    var _ni : bits_n option;
    var _nr : bits_n option;
    var _kmac : bits_n option;
    var sid1 : (int * int * bits_n * bits_n * bits_n) option;
    var _mess : int;
    var unwrap_2 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var acc2 : bool option;
    var sid2 : (int * int * bits_n * bits_n * bits_n) option;
    var unwrap_3 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var acc3 : bool option;
    var sid3 : (int * int * bits_n * bits_n * bits_n) option;
    if (d_State.[ctr1] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

    } else {
      unwrap_1 <- oget d_State.[ctr1];
      (_U, _u, _V, _ltk, acc1, _k, _ni, _nr, _kmac, sid1, _mess) <- unwrap_1;
      if (d_State.[ctr2] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

      } else {
        unwrap_2 <- oget d_State.[ctr2];
        (_U, _u, _V, _ltk, acc2, _k, _ni, _nr, _kmac, sid2, _mess) <- unwrap_2;
        if (d_State.[ctr3] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

        } else {
          unwrap_3 <- oget d_State.[ctr3];
          (_U, _u, _V, _ltk, acc3, _k, _ni, _nr, _kmac, sid3, _mess) <- unwrap_3;
          if (b = false /\ !(ctr1 = ctr2) /\ !(ctr1 = ctr3) /\ !(ctr2 = ctr3)) {
            if (acc1 = acc2 /\ acc2 = acc3 /\ acc3 = Some true) {
              if (sid1 = sid2 /\ sid2 = sid3) {
                ec_result <- Some true;
              } else {
                ec_result <- Some false;
              }
            } else {
              ec_result <- Some false;
            }
          } else {
            ec_result <- Some false;
          }
        }
      }
    }
    return ec_result;
  }

  proc d_AtLeast(sid : (int * int * bits_n * bits_n * bits_n)) : bool option = {
    var ec_result : bool option <- None<:bool>;
    var unwrap_1 : int;
    var unwrap_2 : (int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int);
    var _U : int;
    var _u : bool;
    var _V : int;
    var _ltk : bits_n;
    var acc1 : bool option;
    var _k : bits_n option;
    var _ni : bits_n option;
    var _nr : bits_n option;
    var _kmac : bits_n option;
    var _sid : (int * int * bits_n * bits_n * bits_n) option;
    var _mess : int;
    var unwrap_3 : int;
    if (b = false /\ !(d_First.[sid] = None<:int>) /\ d_Second.[sid] = None<:int>) {
      if (d_First.[sid] = None<:int>) {

      } else {
        unwrap_1 <- oget d_First.[sid];
        if (d_State.[unwrap_1] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option * bits_n option * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {

        } else {
          unwrap_2 <- oget d_State.[unwrap_1];
          (_U, _u, _V, _ltk, acc1, _k, _ni, _nr, _kmac, _sid, _mess) <- unwrap_2;
          if (d_First.[sid] = None<:int>) {

          } else {
            unwrap_3 <- oget d_First.[sid];
            if (acc1 = Some true /\ d_Fresh.[unwrap_3] = Some true) {
              ec_result <- Some true;
            } else {
              ec_result <- Some false;
            }
          }
        }
      }
    } else {
      ec_result <- Some false;
    }
    return ec_result;
  }
}.
