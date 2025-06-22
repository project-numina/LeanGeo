import Qq

import Smt.Translate

namespace Smt.Translate.Rat

open Qq
open Translator Term

@[smt_translate] def translateFalse : Translator := fun (e : Q(Prop)) => match e with
  | ~q(False)  => return appT (symbolT "not") (symbolT "true")
  | _         => return none
