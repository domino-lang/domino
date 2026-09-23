(* PRF: n = n, prf = func_prf *)

require import AllCore Distr FMap Int IntDiv Types.

module PRF = {
  var d_LTK : (int, bits_n) fmap
  var d_H : (int, bool) fmap
  var d_PRF : ((int * (int * int * bits_n * bits_n * bool)), bits_n) fmap
  var kid_ : int
  var b : bool

  proc init(b_ : bool) : unit = {
    d_LTK <- empty;
    d_H <- empty;
    d_PRF <- empty;
    kid_ <- 0;
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

  proc d_Eval(kid : int, x : (int * int * bits_n * bits_n * bool)) : bits_n option = {
    var ec_result : bits_n option;
    var k : bits_n;
    var temp : bits_n;
    var y : bits_n option;
    ec_result <- None;
    if (!(d_LTK.[kid] = None)) {
      if (d_H.[kid] = Some false \/ !b) {
        k <- oget d_LTK.[kid];
        ec_result <- Some (func_prf k x);
      } else {
        if (d_PRF.[(kid, x)] = None) {
          temp <$ dbits_n;
          d_PRF.[(kid, x)] <- temp;
        }
        y <- d_PRF.[(kid, x)];
        if (!(y = None)) {
          ec_result <- Some (oget y);
        }
      }
    }
    return ec_result;
  }

  proc d_Hon(kid : int) : bool option = {
    var ec_result : bool option;
    ec_result <- None;
    if (!(d_H.[kid] = None)) {
      ec_result <- Some (oget d_H.[kid]);
    }
    return ec_result;
  }
}.
