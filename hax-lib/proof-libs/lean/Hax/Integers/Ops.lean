/-
Hax Lean Backend - Cryspen

Support for integer operations
-/

import Hax.Lib
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


/-

# Arithmetic operations

The Rust arithmetic operations have their own notations, using a `?`. They
return a `RustM`, that is `.fail` when arithmetic overflows occur.

-/

/-- The notation typeclass for homogeneous addition that returns a RustM.  This
enables the notation `a +? b : α` where `a : α`, `b : α`. For now, there is no
heterogeneous version -/
class HaxAdd α where
  /-- `a +? b` computes the panicking sum of `a` and `b`.  The meaning of this
  notation is type-dependent. -/
  add : α → α → RustM α

/-- The notation typeclass for homogeneous subtraction that returns a RustM.
This enables the notation `a -? b : α` where `a : α`, `b : α`. For now, there is
no heterogeneous version -/
class HaxSub α where
  /-- `a -? b` computes the panicking subtraction of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  sub : α → α → RustM α

/-- The notation typeclass for homogeneous multiplication that returns a RustM.
This enables the notation `a *? b : RustM α` where `a b : α`. For now, there is
no heterogeneous version -/
class HaxMul α where
  /-- `a *? b` computes the panicking multiplication of `a` and `b`.  The
  meaning of this notation is type-dependent. -/
  mul : α → α → RustM α

/-- The notation typeclass for homogeneous division that returns a RustM.  This
enables the notation `a /? b : RustM α` where `a b : α`. For now, there is no
heterogeneous version -/
class HaxDiv α where
  /-- `a /? b` computes the panicking division of `a` and `b`.  The
  meaning of this notation is type-dependent. -/
  div : α → α → RustM α

/--The notation typeclass for right shift that returns a RustM. It enables the
 notation `a >>>? b : RustM α` where `a : α` and `b : β`. -/
class HaxShiftRight α β where
  /-- `a >>>? b` computes the panicking right-shift of `a` by `b`.  The meaning
  of this notation is type-dependent. It panics if `b` exceeds the size of `a`.
  -/
  shiftRight : α → β → RustM α

/--The notation typeclass for left shift that returns a RustM. It enables the
 notation `a <<<? b : RustM α` where `a : α` and `b : β`. -/
class HaxShiftLeft α β where
  /-- `a <<<? b` computes the panicking left-shift of `a` by `b`.  The meaning
  of this notation is type-dependent. It panics if `b` exceeds the size of `a`.
  -/
  shiftLeft : α → β → RustM α

/-- The notation typeclass for remainder.  This enables the notation `a %? b :
RustM α` where `a b : α`.  -/
class HaxRem α where
  /-- `a %? b` computes the panicking remainder upon dividing `a` by `b`.  The
  meaning of this notation is type-dependent. It panics if b is zero -/
  rem : α → α → RustM α

@[inherit_doc] infixl:65 " +? "   => HaxAdd.add
@[inherit_doc] infixl:65 " -? "   => HaxSub.sub
@[inherit_doc] infixl:70 " *? "   => HaxMul.mul
@[inherit_doc] infixl:75 " >>>? " => HaxShiftRight.shiftRight
@[inherit_doc] infixl:75 " <<<? " => HaxShiftLeft.shiftLeft
@[inherit_doc] infixl:70 " %? "   => HaxRem.rem
@[inherit_doc] infixl:70 " /? "   => HaxDiv.div

open Lean in
macro "declare_Hax_int_ops" s:(&"signed" <|> &"unsigned") typeName:ident width:term : command => do

  let signed ← match s.raw[0].getKind with
  | `signed => pure true
  | `unsigned => pure false
  | _ => throw .unsupportedSyntax

  let mut cmds ← Syntax.getArgs <$> `(
    /-- Addition on Rust integers. Panics on overflow. -/
    instance : HaxAdd $typeName where
      add x y :=
        if ($(mkIdent (if signed then `BitVec.saddOverflow else `BitVec.uaddOverflow)) x.toBitVec y.toBitVec) then
          .fail .integerOverflow
        else pure (x + y)

    /-- Subtraction on Rust integers. Panics on overflow. -/
    instance : HaxSub $typeName where
      sub x y :=
        if ($(mkIdent (if signed then `BitVec.ssubOverflow else `BitVec.usubOverflow)) x.toBitVec y.toBitVec) then
          .fail .integerOverflow
        else pure (x - y)

    /-- Multiplication on Rust integers. Panics on overflow. -/
    instance : HaxMul $typeName where
      mul x y :=
        if ($(mkIdent (if signed then `BitVec.smulOverflow else `BitVec.umulOverflow)) x.toBitVec y.toBitVec) then
          .fail .integerOverflow
        else pure (x * y)
  )
  if signed then
    cmds := cmds.append $ ← Syntax.getArgs <$> `(
      /- Division of signed Rust integers. Panics on overflow (when x is IntMin and `y = -1`)
        and when dividing by zero. -/
      instance : HaxDiv $typeName where
        div x y :=
          if BitVec.sdivOverflow x.toBitVec y.toBitVec then .fail .integerOverflow
          else if y = 0 then .fail .divisionByZero
          else pure (x / y)

      /- Remainder of signed Rust integers. Panics on overflow (when x is IntMin and `y = -1`)
        and when the modulus is zero. -/
      instance : HaxRem $typeName where
        rem x y :=
          if BitVec.sdivOverflow x.toBitVec y.toBitVec then .fail .integerOverflow
          else if y = 0 then .fail .divisionByZero
          else pure (x % y)

      /- Right shifting on signed integers. Panics when shifting by a negative number,
        or when shifting by more than the size. -/
      instance : HaxShiftRight $typeName $typeName where
        shiftRight x y :=
          if 0 ≤ y.toInt && y.toInt < Int.ofNat $width then
            pure (x >>> y)
          else
            .fail .integerOverflow

      /- Left shifting on signed integers. Panics when shifting by a negative number,
        or when shifting by more than the size. -/
      instance : HaxShiftLeft $typeName $typeName where
        shiftLeft x y :=
          if 0 ≤ y.toInt && y.toInt < Int.ofNat $width then
            pure (x <<< y)
          else
            .fail .integerOverflow
    )
  else -- unsigned
    cmds := cmds.append $ ← Syntax.getArgs <$> `(
      /-- Division on unsigned Rust integers. Panics when dividing by zero.  -/
      instance : HaxDiv $typeName where
        div x y :=
          if y = 0 then .fail .divisionByZero
          else pure (x / y)

      /-- Division on unsigned Rust integers. Panics when the modulus is zero. -/
      instance : HaxRem $typeName where
        rem x y :=
          if y = 0 then .fail .divisionByZero
          else pure (x % y)

      /-- Right shift on unsigned Rust integers. Panics when shifting by more than the size. -/
      instance: HaxShiftRight $typeName $typeName where
        shiftRight x y :=
          if $width ≤ y.toNat then .fail .integerOverflow
          else pure (x >>> y)

      /-- Left shift on unsigned Rust integers. Panics when shifting by more than the size. -/
      instance: HaxShiftLeft $typeName $typeName where
        shiftLeft x y :=
          if $width ≤ y.toNat then .fail .integerOverflow
          else pure (x <<< y)
    )
  return ⟨mkNullNode cmds⟩

declare_Hax_int_ops unsigned UInt8 8
declare_Hax_int_ops unsigned UInt16 16
declare_Hax_int_ops unsigned UInt32 32
declare_Hax_int_ops unsigned UInt64 64
declare_Hax_int_ops unsigned USize System.Platform.numBits
declare_Hax_int_ops signed Int8 8
declare_Hax_int_ops signed Int16 16
declare_Hax_int_ops signed Int32 32
declare_Hax_int_ops signed Int64 64
declare_Hax_int_ops signed ISize System.Platform.numBits

/- Check that all operations are implemented -/

class Operations α where
  [instHaxAdd: HaxAdd α]
  [instHaxSub: HaxSub α]
  [instHaxMul: HaxMul α]
  [instHaxDiv: HaxDiv α]
  [instHaxRem: HaxRem α]
  [instHaxShiftRight: HaxShiftRight α α]
  [instHaxShiftLeft: HaxShiftLeft α α]

instance : Operations u8 where
instance : Operations u16 where
instance : Operations u32 where
instance : Operations u64 where
instance : Operations usize where
instance : Operations i8 where
instance : Operations i16 where
instance : Operations i32 where
instance : Operations i64 where
instance : Operations isize where

-- Custom instances
@[simp, spec]
instance : HaxShiftRight u64 i32 where
  shiftRight x y :=
    if 0 ≤ y && y < 64 then pure (x >>> y.toNatClampNeg.toUInt64)
    else .fail .integerOverflow

-- Custom instances
@[simp, spec]
instance : HaxShiftRight i64 i32 where
  shiftRight x y :=
    if 0 ≤ y && y < 64 then pure (x >>> y.toInt64)
    else .fail .integerOverflow
