import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive ast where
  | Foo (_ : Sigma (fun k_n => (Int × Int × Int × (BitVec k_n))))
  | Bar (_ : (Int × Int × Sigma (fun k_n => (Int × (BitVec k_n)))))
  deriving Inhabited, BEq, Repr
  open ast

inductive ast' where
  | Foo' (_ : Sigma (fun k_n => (Int × Int × (BitVec k_n) × Int)))
  deriving Inhabited, BEq, Repr
  open ast'

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception


XXXXXXXXX

import Sail
import Out.Defs
import Out.Specialization
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

namespace Out.Functions

open option
open ast'
open ast

/-- Type quantifiers: k_ex2098_ : Bool, k_ex2097_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (((n <b 0) && (m >b 0)) : Bool)
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    (if (((n >b 0) && (m <b 0)) : Bool)
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m))

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if ((l ≥b n) : Bool)
  then ((sail_ones n) <<< i)
  else
    (let one : (BitVec n) := (sail_mask n (1#1 : (BitVec 1)))
    (((one <<< l) - one) <<< i))

/-- Type quantifiers: n : Nat, n > 0 -/
def to_bytes_le {n : _} (b : (BitVec (8 * n))) : (Vector (BitVec 8) n) := Id.run do
  let res := (vectorInit (BitVec.zero 8))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (vectorUpdate res i (Sail.BitVec.extractLsb b ((8 *i i) +i 7) (8 *i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n > 0 -/
def from_bytes_le {n : _} (v : (Vector (BitVec 8) n)) : (BitVec (8 * n)) := Id.run do
  let res := (BitVec.zero (8 *i n))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (Sail.BitVec.updateSubrange res ((8 *i i) +i 7) (8 *i i) (GetElem?.getElem! v i))
  (pure loop_vars)

/-- Type quantifiers: k_a : Type -/
def is_none (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => false
  | none => true

/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => true
  | none => false

/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toFormatted x))

/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))

def test1 (x : ast) : Int :=
  match x with
  | .Foo (a, b, _, d) => ((a +i b) +i (BitVec.toNatInt d))
  | .Bar (a, b, (_, d)) => ((a +i b) +i (BitVec.toNatInt d))

def test2 (x : ast) : Int :=
  match x with
  | .Foo (a, b, _, d) => ((a +i b) +i (BitVec.toNatInt d))
  | .Bar (a, b, y) =>
    (match y with
    | (_, d) => ((a +i b) +i (BitVec.toNatInt d)))

def test3 (x : ast) : Int :=
  match x with
  | .Foo a =>
    (match a with
    | (a, b, _, d) => ((a +i b) +i (BitVec.toNatInt d)))
  | .Bar _ => 1

/-- Type quantifiers: i : Int -/
def test4 (i : Int) (v : (BitVec 16)) : ast :=
  let x : Sigma (fun k_n => (Int × Int × Int × (BitVec k_n))) := (i, i, 16, v)
  (Foo x)

/-- Type quantifiers: i : Int -/
def test4b (i : Int) (v : (BitVec 16)) : ast' :=
  let x : Sigma (fun k_n => (Int × Int × (BitVec k_n) × Int)) := (i, i, v, 16)
  (Foo' x)

def test5 (_ : Unit) : SailM Unit := do
  let x := (Foo (3, 3, 16, 0x1234#16))
  let y := (test4 3 0x1234#16)
  assert (x == y) "existentials1.sail:46.15-46.16"
  assert ((test1 x) == (test2 x)) "existentials1.sail:47.29-47.30"

/-- Type quantifiers: k_ex2348_ : Nat, x : Int, k_ex2348_ ∈ {16, 32} -/
def test6 (x : Int) (t : (Nat × (BitVec k_ex2348_))) : Int :=
  let i : Int :=
    match t with
    | (n, v) => (BitVec.toNatInt v)
  (i +i x)

/-- Type quantifiers: x : Int -/
def test7 (x : Int) (tuple_1 : (Int × Sigma (fun k_n => (Int × (BitVec k_n))))) : Int :=
  let (_, t) := tuple_1
  let i : Int :=
    match t with
    | (n, v) => (BitVec.toNatInt v)
  (i +i x)

/-- Type quantifiers: x : Int -/
def test8 (x : Int) (t : (Int × Sigma (fun k_n => (Int × (BitVec k_n))))) : Int :=
  let i : Int :=
    match t with
    | (_, (n, v)) => (BitVec.toNatInt v)
  (i +i x)

/-- Type quantifiers: v : Int, n : Int -/
def test9 (n : Int) (v : Int) : Sigma (fun k_n => (Int × (BitVec k_n))) :=
  let n' :=
    if ((n ≤b 0) : Bool)
    then 1
    else n
  (n', (BitVec.addInt (BitVec.zero n') v))

/-- Type quantifiers: v : Int, n : Int -/
def test10 (n : Int) (v : Int) : (Int × Sigma (fun k_n => (Int × (BitVec k_n)))) :=
  let n' :=
    if ((n ≤b 0) : Bool)
    then 1
    else n
  (v, (n', (BitVec.addInt (BitVec.zero n') v)))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
