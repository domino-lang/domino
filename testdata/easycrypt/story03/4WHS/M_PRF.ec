(* M_PRF: n = n, prf = func_prf *)

require import AllCore Distr FMap Int IntDiv Types.

module M_PRF = {
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

  proc d_Eval(kid : int, x : (int * int * bits_n * bits_n * bool)) : bits_n option = {
    var ec_result : bits_n option <- None<:bits_n>;
    var unwrap_1 : bits_n;
    var k : bits_n;
    var temp : bits_n;
    var y : bits_n option;
    var unwrap_2 : bits_n;
    if (!(d_LTK.[kid] = None<:bits_n>)) {
      if (d_H.[kid] = Some false \/ !b) {
        if (d_LTK.[kid] = None<:bits_n>) {

        } else {
          unwrap_1 <- oget d_LTK.[kid];
          k <- unwrap_1;
          ec_result <- Some (func_prf k x);
        }
      } else {
        if (d_PRF.[(kid, x)] = None<:bits_n>) {
          temp <$ dbits_n;
          d_PRF.[(kid, x)] <- temp;
          y <- d_PRF.[(kid, x)];
          if (y = None<:bits_n>) {

          } else {
            unwrap_2 <- oget y;
            ec_result <- Some unwrap_2;
          }
        } else {
          y <- d_PRF.[(kid, x)];
          if (y = None<:bits_n>) {

          } else {
            unwrap_2 <- oget y;
            ec_result <- Some unwrap_2;
          }
        }
      }
    } else {

    }
    return ec_result;
  }

  proc d_Hon(kid : int) : bool option = {
    var ec_result : bool option <- None<:bool>;
    var unwrap_1 : bool;
    if (!(d_H.[kid] = None<:bool>)) {
      if (d_H.[kid] = None<:bool>) {

      } else {
        unwrap_1 <- oget d_H.[kid];
        ec_result <- Some unwrap_1;
      }
    } else {

    }
    return ec_result;
  }
}.
