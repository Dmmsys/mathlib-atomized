/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Lean.Meta.Basic
public import Mathlib.Init

/-!
# Datatypes for bicategory like structures

This file defines the basic datatypes for bicategory like structures. We will use these datatypes
to write tactics that can be applied to both monoidal categories and bicategories:
- `Obj`: objects type
- `Atom₁`: atomic 1-morphisms type
- `Mor₁`: 1-morphisms type
- `Atom`: atomic non-structural 2-morphisms type
- `Mor₂`: 2-morphisms type
- `AtomIso`: atomic non-structural 2-isomorphisms type
- `Mor₂Iso`: 2-isomorphisms type
- `NormalizedHom`: normalized 1-morphisms type

A term of these datatypes wraps the corresponding `Expr` term, which can be extracted by
e.g. `η.e` for `η : Mor₂`.

The operations of these datatypes are defined in a monad `m` with the corresponding typeclasses:
- `MonadMor₁`: operations on `Mor₁`
- `MonadMor₂Iso`: operations on `Mor₂Iso`
- `MonadMor₂`: operations on `Mor₂`

For example, a monad `m` with `[MonadMor₂ m]` provides the operation
`MonadMor₂.comp₂M : Mor₂Iso → Mor₂Iso → m Mor₂Iso`, which constructs the expression for the
composition `η ≫ θ` of 2-morphisms `η` and `θ` in the monad `m`.

-/

public meta section

open Lean Meta

namespace Mathlib.Tactic

namespace BicategoryLike

/--
Definition of `Obj` / `Obj` 的定义

English:
structure Obj
  parameters: where
  axioms and operations (1):
    - e? : Option Expr

中文:
结构 Obj
  参数: where
  公理与运算 (1 个):
    - e? : Option Expr
-/
structure Obj where
  /-- Extracts a lean expression from an `Obj` term. Return `none` in the monoidal
  category context. -/
  e? : Option Expr
  deriving Inhabited

/--
Definition of `Obj.e` / `Obj.e` 的定义

English:
definition Obj.e
  signature: (a : Obj)
  body: a.e?.get!

中文:
定义 Obj.e
  签名: (a : Obj)
  定义体: a.e?.get!
-/
def Obj.e (a : Obj) : Expr :=
  a.e?.get!

/--
Definition of `Atom₁` / `Atom₁` 的定义

English:
structure Atom₁
  parameters: : Type where
  axioms and operations (3):
    - e : Expr
    - src : Obj
    - tgt : Obj

中文:
结构 Atom₁
  参数: : Type where
  公理与运算 (3 个):
    - e : Expr
    - src : Obj
    - tgt : Obj
-/
structure Atom₁ : Type where
  /-- Extract a lean expression from an `Atom₁` term. -/
  e : Expr
  /-- The domain of the 1-morphism. -/
  src : Obj
  /-- The codomain of the 1-morphism. -/
  tgt : Obj
  deriving Inhabited

/--
Definition of `MkAtom₁` / `MkAtom₁` 的定义

English:
class MkAtom₁
  parameters: (m : Type -> Type)
  axioms and operations (1):
    - ofExpr((e : Expr)) : m Atom₁

中文:
类 MkAtom₁
  参数: (m : Type -> Type)
  公理与运算 (1 个):
    - ofExpr((e : Expr)) : m Atom₁
-/
class MkAtom₁ (m : Type -> Type) where
  /-- Construct a `Atom₁` term from a lean expression. -/
  ofExpr (e : Expr) : m Atom₁

/--
Inductive type `Mor₁` / 归纳类型 `Mor₁`

English:
inductive Mor₁
  parameters: : Type
  constructors (3):
    - id: (e : Expr) (a : Obj) : Mor₁
    - comp: (e : Expr) : Mor₁ -> Mor₁ -> Mor₁
    - of: Atom₁ -> Mor₁

中文:
归纳类型 Mor₁
  参数: : Type
  构造子 (3 个):
    - id: (e : Expr) (a : Obj) : Mor₁
    - comp: (e : Expr) : Mor₁ -> Mor₁ -> Mor₁
    - of: Atom₁ -> Mor₁
-/
inductive Mor₁ : Type
  /-- `id e a` is the expression for `𝟙 a`, where `e` is the underlying lean expression. -/
  | id (e : Expr) (a : Obj) : Mor₁
  /-- `comp e f g` is the expression for `f ≫ g`, where `e` is the underlying lean expression. -/
  | comp (e : Expr) : Mor₁ -> Mor₁ -> Mor₁
  /-- The expression for an atomic 1-morphism. -/
  | of : Atom₁ -> Mor₁
  deriving Inhabited

/--
Definition of `MkMor₁` / `MkMor₁` 的定义

English:
class MkMor₁
  parameters: (m : Type -> Type)
  axioms and operations (1):
    - ofExpr((e : Expr)) : m Mor₁

中文:
类 MkMor₁
  参数: (m : Type -> Type)
  公理与运算 (1 个):
    - ofExpr((e : Expr)) : m Mor₁
-/
class MkMor₁ (m : Type -> Type) where
  /-- Construct a `Mor₁` term from a lean expression. -/
  ofExpr (e : Expr) : m Mor₁

/--
Definition of `Mor₁.e` / `Mor₁.e` 的定义

English:
definition Mor₁.e
  signature: : Mor₁ -> Expr

中文:
定义 Mor₁.e
  签名: : Mor₁ -> Expr
-/
def Mor₁.e : Mor₁ -> Expr
  | .id e _ => e
  | .comp e _ _ => e
  | .of a => a.e

/--
Definition of `Mor₁.src` / `Mor₁.src` 的定义

English:
definition Mor₁.src
  signature: : Mor₁ -> Obj

中文:
定义 Mor₁.src
  签名: : Mor₁ -> Obj
-/
def Mor₁.src : Mor₁ -> Obj
  | .id _ a => a
  | .comp _ f _ => f.src
  | .of f => f.src

/--
Definition of `Mor₁.tgt` / `Mor₁.tgt` 的定义

English:
definition Mor₁.tgt
  signature: : Mor₁ -> Obj

中文:
定义 Mor₁.tgt
  签名: : Mor₁ -> Obj
-/
def Mor₁.tgt : Mor₁ -> Obj
  | .id _ a => a
  | .comp _ _ g => g.tgt
  | .of f => f.tgt

/--
Definition of `Mor₁.toList` / `Mor₁.toList` 的定义

English:
definition Mor₁.toList
  signature: : Mor₁ -> List Atom₁

中文:
定义 Mor₁.toList
  签名: : Mor₁ -> List Atom₁
-/
def Mor₁.toList : Mor₁ -> List Atom₁
  | .id _ _ => []
  | .comp _ f g => f.toList ++ g.toList
  | .of f => [f]

/--
Definition of `MonadMor₁` / `MonadMor₁` 的定义

English:
class MonadMor₁
  parameters: (m : Type -> Type)
  axioms and operations (2):
    - id₁M((a : Obj)) : m Mor₁
    - comp₁M((f g : Mor₁)) : m Mor₁

中文:
类 MonadMor₁
  参数: (m : Type -> Type)
  公理与运算 (2 个):
    - id₁M((a : Obj)) : m Mor₁
    - comp₁M((f g : Mor₁)) : m Mor₁
-/
class MonadMor₁ (m : Type -> Type) where
  /-- The expression for `𝟙 a`. -/
  id₁M (a : Obj) : m Mor₁
  /-- The expression for `f ≫ g`. -/
  comp₁M (f g : Mor₁) : m Mor₁

/--
Definition of `CoherenceHom` / `CoherenceHom` 的定义

English:
structure CoherenceHom
  parameters: where
  axioms and operations (5):
    - e : Expr
    - src : Mor₁
    - tgt : Mor₁
    - inst : Expr
    - unfold : Expr

中文:
结构 CoherenceHom
  参数: where
  公理与运算 (5 个):
    - e : Expr
    - src : Mor₁
    - tgt : Mor₁
    - inst : Expr
    - unfold : Expr
-/
structure CoherenceHom where
  /-- The underlying lean expression of a coherence isomorphism. -/
  e : Expr
  /-- The domain of a coherence isomorphism. -/
  src : Mor₁
  /-- The codomain of a coherence isomorphism. -/
  tgt : Mor₁
  /-- The `BicategoricalCoherence` instance. -/
  inst : Expr
  /-- Extract the structural 2-isomorphism. -/
  unfold : Expr
  deriving Inhabited

/--
Definition of `AtomIso` / `AtomIso` 的定义

English:
structure AtomIso
  parameters: where
  axioms and operations (3):
    - e : Expr
    - src : Mor₁
    - tgt : Mor₁

中文:
结构 AtomIso
  参数: where
  公理与运算 (3 个):
    - e : Expr
    - src : Mor₁
    - tgt : Mor₁
-/
structure AtomIso where
  /-- The underlying lean expression of an `AtomIso` term. -/
  e : Expr
  /-- The domain of a 2-isomorphism. -/
  src : Mor₁
  /-- The codomain of a 2-isomorphism. -/
  tgt : Mor₁
  deriving Inhabited

/--
Inductive type `StructuralAtom` / 归纳类型 `StructuralAtom`

English:
inductive StructuralAtom
  parameters: : Type
  constructors (5):
    - associator: (e : Expr) (f g h : Mor₁) : StructuralAtom
    - leftUnitor: (e : Expr) (f : Mor₁) : StructuralAtom
    - rightUnitor: (e : Expr) (f : Mor₁) : StructuralAtom
    - id: (e : Expr) (f : Mor₁) : StructuralAtom
    - coherenceHom: (α : CoherenceHom) : StructuralAtom

中文:
归纳类型 StructuralAtom
  参数: : Type
  构造子 (5 个):
    - associator: (e : Expr) (f g h : Mor₁) : StructuralAtom
    - leftUnitor: (e : Expr) (f : Mor₁) : StructuralAtom
    - rightUnitor: (e : Expr) (f : Mor₁) : StructuralAtom
    - id: (e : Expr) (f : Mor₁) : StructuralAtom
    - coherenceHom: (α : CoherenceHom) : StructuralAtom
-/
inductive StructuralAtom : Type
  /-- The expression for the associator `α_ f g h`. -/
  | associator (e : Expr) (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `λ_ f`. -/
  | leftUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `ρ_ f`. -/
  | rightUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  | id (e : Expr) (f : Mor₁) : StructuralAtom
  | coherenceHom (α : CoherenceHom) : StructuralAtom
  deriving Inhabited

/--
Inductive type `Mor₂Iso` / 归纳类型 `Mor₂Iso`

English:
inductive Mor₂Iso
  parameters: : Type where
  constructors (8):
    - structuralAtom: (α : StructuralAtom) : Mor₂Iso
    - comp: (e : Expr) (f g h : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
    - whiskerLeft: (e : Expr) (f g h : Mor₁) (η : Mor₂Iso) : Mor₂Iso
    - whiskerRight: (e : Expr) (f g : Mor₁) (η : Mor₂Iso) (h : Mor₁) : Mor₂Iso
    - horizontalComp: (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
    - inv: (e : Expr) (f g : Mor₁) (η : Mor₂Iso) : Mor₂Iso
    - coherenceComp: (e : Expr) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂Iso) : Mor₂Iso
    - of: (η : AtomIso) : Mor₂Iso

中文:
归纳类型 Mor₂Iso
  参数: : Type where
  构造子 (8 个):
    - structuralAtom: (α : StructuralAtom) : Mor₂Iso
    - comp: (e : Expr) (f g h : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
    - whiskerLeft: (e : Expr) (f g h : Mor₁) (η : Mor₂Iso) : Mor₂Iso
    - whiskerRight: (e : Expr) (f g : Mor₁) (η : Mor₂Iso) (h : Mor₁) : Mor₂Iso
    - horizontalComp: (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
    - inv: (e : Expr) (f g : Mor₁) (η : Mor₂Iso) : Mor₂Iso
    - coherenceComp: (e : Expr) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂Iso) : Mor₂Iso
    - of: (η : AtomIso) : Mor₂Iso
-/
inductive Mor₂Iso : Type where
  | structuralAtom (α : StructuralAtom) : Mor₂Iso
  | comp (e : Expr) (f g h : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | whiskerLeft (e : Expr) (f g h : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | whiskerRight (e : Expr) (f g : Mor₁) (η : Mor₂Iso) (h : Mor₁) : Mor₂Iso
  | horizontalComp (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | inv (e : Expr) (f g : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | coherenceComp (e : Expr) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂Iso) : Mor₂Iso
  | of (η : AtomIso) : Mor₂Iso
  deriving Inhabited

/--
Definition of `MonadCoherehnceHom` / `MonadCoherehnceHom` 的定义

English:
class MonadCoherehnceHom
  parameters: (m : Type -> Type)
  axioms and operations (1):
    - unfoldM((α : CoherenceHom)) : m Mor₂Iso

中文:
类 MonadCoherehnceHom
  参数: (m : Type -> Type)
  公理与运算 (1 个):
    - unfoldM((α : CoherenceHom)) : m Mor₂Iso
-/
class MonadCoherehnceHom (m : Type -> Type) where
  /-- Unfold a coherence isomorphism. -/
  unfoldM (α : CoherenceHom) : m Mor₂Iso

/--
Definition of `StructuralAtom.e` / `StructuralAtom.e` 的定义

English:
definition StructuralAtom.e
  signature: : StructuralAtom -> Expr

中文:
定义 StructuralAtom.e
  签名: : StructuralAtom -> Expr
-/
def StructuralAtom.e : StructuralAtom -> Expr
  | .associator e .. => e
  | .leftUnitor e .. => e
  | .rightUnitor e .. => e
  | .id e .. => e
  | .coherenceHom α => α.e

open MonadMor₁

variable {m : Type -> Type} [Monad m]

/--
Definition of `StructuralAtom.srcM` / `StructuralAtom.srcM` 的定义

English:
definition StructuralAtom.srcM
  signature: [MonadMor₁ m]

中文:
定义 StructuralAtom.srcM
  签名: [MonadMor₁ m]
-/
def StructuralAtom.srcM [MonadMor₁ m] : StructuralAtom -> m Mor₁
  | .associator _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => do comp₁M (← id₁M f.src) f
  | .rightUnitor _ f => do comp₁M f (← id₁M f.tgt)
  | .id _ f => return f
  | .coherenceHom α => return α.src

/--
Definition of `StructuralAtom.tgtM` / `StructuralAtom.tgtM` 的定义

English:
definition StructuralAtom.tgtM
  signature: [MonadMor₁ m]

中文:
定义 StructuralAtom.tgtM
  签名: [MonadMor₁ m]
-/
def StructuralAtom.tgtM [MonadMor₁ m] : StructuralAtom -> m Mor₁
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .leftUnitor _ f => return f
  | .rightUnitor _ f => return f
  | .id _ f => return f
  | .coherenceHom α => return α.tgt

/--
Definition of `Mor₂Iso.e` / `Mor₂Iso.e` 的定义

English:
definition Mor₂Iso.e
  signature: : Mor₂Iso -> Expr

中文:
定义 Mor₂Iso.e
  签名: : Mor₂Iso -> Expr
-/
def Mor₂Iso.e : Mor₂Iso -> Expr
  | .structuralAtom α => α.e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .inv e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e

/--
Definition of `Mor₂Iso.srcM` / `Mor₂Iso.srcM` 的定义

English:
definition Mor₂Iso.srcM
  signature: {m : Type -> Type} [Monad m] [MonadMor₁ m]

中文:
定义 Mor₂Iso.srcM
  签名: {m : Type -> Type} [Monad m] [MonadMor₁ m]
-/
def Mor₂Iso.srcM {m : Type -> Type} [Monad m] [MonadMor₁ m] : Mor₂Iso -> m Mor₁
  | .structuralAtom α => α.srcM
  | .comp _ f .. => return f
  | .whiskerLeft _ f g .. => do comp₁M f g
  | .whiskerRight _ f _ _ h => do comp₁M f h
  | .horizontalComp _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .inv _ _ g _ => return g
  | .coherenceComp _ f .. => return f
  | .of η => return η.src

/--
Definition of `Mor₂Iso.tgtM` / `Mor₂Iso.tgtM` 的定义

English:
definition Mor₂Iso.tgtM
  signature: {m : Type -> Type} [Monad m] [MonadMor₁ m]

中文:
定义 Mor₂Iso.tgtM
  签名: {m : Type -> Type} [Monad m] [MonadMor₁ m]

Depends on / 依赖: Countable, OrderTopology
-/
def Mor₂Iso.tgtM {m : Type -> Type} [Monad m] [MonadMor₁ m] : Mor₂Iso -> m Mor₁
  | .structuralAtom α => α.tgtM
  | .comp _ _ _ h .. => return h
  | .whiskerLeft _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .inv _ f _ _ => return f
  | .coherenceComp _ _ _ _ i .. => return i
  | .of η => return η.tgt

/--
Definition of `MonadMor₂Iso` / `MonadMor₂Iso` 的定义

English:
class MonadMor₂Iso
  parameters: (m : Type -> Type)
  axioms and operations (11):
    - associatorM((f g h : Mor₁)) : m StructuralAtom
    - leftUnitorM((f : Mor₁)) : m StructuralAtom
    - rightUnitorM((f : Mor₁)) : m StructuralAtom
    - id₂M((f : Mor₁)) : m StructuralAtom
    - coherenceHomM((f g : Mor₁) (inst : Expr)) : m CoherenceHom
    - comp₂M((η θ : Mor₂Iso)) : m Mor₂Iso
    - whiskerLeftM((f : Mor₁) (η : Mor₂Iso)) : m Mor₂Iso
    - whiskerRightM((η : Mor₂Iso) (h : Mor₁)) : m Mor₂Iso
    - horizontalCompM((η θ : Mor₂Iso)) : m Mor₂Iso
    - symmM((η : Mor₂Iso)) : m Mor₂Iso
    - coherenceCompM((α : CoherenceHom) (η θ : Mor₂Iso)) : m Mor₂Iso

中文:
类 MonadMor₂Iso
  参数: (m : Type -> Type)
  公理与运算 (11 个):
    - associatorM((f g h : Mor₁)) : m StructuralAtom
    - leftUnitorM((f : Mor₁)) : m StructuralAtom
    - rightUnitorM((f : Mor₁)) : m StructuralAtom
    - id₂M((f : Mor₁)) : m StructuralAtom
    - coherenceHomM((f g : Mor₁) (inst : Expr)) : m CoherenceHom
    - comp₂M((η θ : Mor₂Iso)) : m Mor₂Iso
    - whiskerLeftM((f : Mor₁) (η : Mor₂Iso)) : m Mor₂Iso
    - whiskerRightM((η : Mor₂Iso) (h : Mor₁)) : m Mor₂Iso
    - horizontalCompM((η θ : Mor₂Iso)) : m Mor₂Iso
    - symmM((η : Mor₂Iso)) : m Mor₂Iso
    - coherenceCompM((α : CoherenceHom) (η θ : Mor₂Iso)) : m Mor₂Iso
-/
class MonadMor₂Iso (m : Type -> Type) where
  /-- The expression for the associator `α_ f g h`. -/
  associatorM (f g h : Mor₁) : m StructuralAtom
  /-- The expression for the left unitor `λ_ f`. -/
  leftUnitorM (f : Mor₁) : m StructuralAtom
  /-- The expression for the right unitor `ρ_ f`. -/
  rightUnitorM (f : Mor₁) : m StructuralAtom
  /-- The expression for the identity `Iso.refl f`. -/
  id₂M (f : Mor₁) : m StructuralAtom
  /-- The expression for the coherence isomorphism `⊗𝟙 : f ⟶ g`. -/
  coherenceHomM (f g : Mor₁) (inst : Expr) : m CoherenceHom
  /-- The expression for the composition `η ≪≫ θ`. -/
  comp₂M (η θ : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the left whiskering `whiskerLeftIso f η`. -/
  whiskerLeftM (f : Mor₁) (η : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the right whiskering `whiskerRightIso η h`. -/
  whiskerRightM (η : Mor₂Iso) (h : Mor₁) : m Mor₂Iso
  /-- The expression for the horizontal composition `η ◫ θ`. -/
  horizontalCompM (η θ : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the inverse `Iso.symm η`. -/
  symmM (η : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the coherence composition `η ≪⊗≫ θ := η ≪≫ α ≪≫ θ`. -/
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂Iso) : m Mor₂Iso

namespace MonadMor₂Iso

variable {m : Type -> Type} [Monad m] [MonadMor₂Iso m]

/--
Definition of `associatorM'` / `associatorM'` 的定义

English:
definition associatorM'
  signature: (f g h : Mor₁)
  body: do
return .structuralAtom ← MonadMor₂Iso.associatorM f g h

中文:
定义 associatorM'
  签名: (f g h : Mor₁)
  定义体: do
return .structuralAtom ← MonadMor₂Iso.associatorM f g h
-/
def associatorM' (f g h : Mor₁) : m Mor₂Iso := do
return .structuralAtom ← MonadMor₂Iso.associatorM f g h

/--
Definition of `leftUnitorM'` / `leftUnitorM'` 的定义

English:
definition leftUnitorM'
  signature: (f : Mor₁)
  body: do
return .structuralAtom ← MonadMor₂Iso.leftUnitorM f

中文:
定义 leftUnitorM'
  签名: (f : Mor₁)
  定义体: do
return .structuralAtom ← MonadMor₂Iso.leftUnitorM f
-/
def leftUnitorM' (f : Mor₁) : m Mor₂Iso := do
return .structuralAtom ← MonadMor₂Iso.leftUnitorM f

/--
Definition of `rightUnitorM'` / `rightUnitorM'` 的定义

English:
definition rightUnitorM'
  signature: (f : Mor₁)
  body: do
return .structuralAtom ← MonadMor₂Iso.rightUnitorM f

中文:
定义 rightUnitorM'
  签名: (f : Mor₁)
  定义体: do
return .structuralAtom ← MonadMor₂Iso.rightUnitorM f
-/
def rightUnitorM' (f : Mor₁) : m Mor₂Iso := do
return .structuralAtom ← MonadMor₂Iso.rightUnitorM f

/--
Definition of `id₂M'` / `id₂M'` 的定义

English:
definition id₂M'
  signature: (f : Mor₁)
  body: do
return .structuralAtom ← MonadMor₂Iso.id₂M f

中文:
定义 id₂M'
  签名: (f : Mor₁)
  定义体: do
return .structuralAtom ← MonadMor₂Iso.id₂M f
-/
def id₂M' (f : Mor₁) : m Mor₂Iso := do
return .structuralAtom ← MonadMor₂Iso.id₂M f

/--
Definition of `coherenceHomM'` / `coherenceHomM'` 的定义

English:
definition coherenceHomM'
  signature: (f g : Mor₁) (inst : Expr)
  body: do
return .structuralAtom .coherenceHom ← MonadMor₂Iso.coherenceHomM f g inst

中文:
定义 coherenceHomM'
  签名: (f g : Mor₁) (inst : Expr)
  定义体: do
return .structuralAtom .coherenceHom ← MonadMor₂Iso.coherenceHomM f g inst
-/
def coherenceHomM' (f g : Mor₁) (inst : Expr) : m Mor₂Iso := do
return .structuralAtom .coherenceHom ← MonadMor₂Iso.coherenceHomM f g inst

end MonadMor₂Iso

/--
Definition of `Atom` / `Atom` 的定义

English:
structure Atom
  parameters: where
  axioms and operations (3):
    - e : Expr
    - src : Mor₁
    - tgt : Mor₁

中文:
结构 Atom
  参数: where
  公理与运算 (3 个):
    - e : Expr
    - src : Mor₁
    - tgt : Mor₁
-/
structure Atom where
  /-- Extract a lean expression from an `Atom` expression. -/
  e : Expr
  /-- The domain of a 2-morphism. -/
  src : Mor₁
  /-- The codomain of a 2-morphism. -/
  tgt : Mor₁
  deriving Inhabited

/--
Definition of `IsoLift` / `IsoLift` 的定义

English:
structure IsoLift
  parameters: where
  axioms and operations (2):
    - e : Mor₂Iso
    - eq : Expr

中文:
结构 IsoLift
  参数: where
  公理与运算 (2 个):
    - e : Mor₂Iso
    - eq : Expr
-/
structure IsoLift where
  /-- The expression for the 2-isomorphism. -/
  e : Mor₂Iso
  /-- The expression for the proof that the forward direction of the 2-isomorphism is equal to
  the original 2-morphism. -/
  eq : Expr

/--
Inductive type `Mor₂` / 归纳类型 `Mor₂`

English:
inductive Mor₂
  parameters: : Type where
  constructors (9):
    - isoHom: (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
    - isoInv: (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
    - id: (e : Expr) (isoLift : IsoLift) (f : Mor₁) : Mor₂
    - comp: (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η θ : Mor₂) : Mor₂
    - whiskerLeft: (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η : Mor₂) : Mor₂
    - whiskerRight: (e : Expr) (isoLift? : Option IsoLift) (f g : Mor₁) (η : Mor₂) (h : Mor₁) : Mor₂
    - horizontalComp: (e : Expr) (isoLift? : Option IsoLift) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂) : Mor₂
    - coherenceComp: (e : Expr) (isoLift? : Option IsoLift) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂) : Mor₂
    - of: (η : Atom) : Mor₂

中文:
归纳类型 Mor₂
  参数: : Type where
  构造子 (9 个):
    - isoHom: (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
    - isoInv: (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
    - id: (e : Expr) (isoLift : IsoLift) (f : Mor₁) : Mor₂
    - comp: (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η θ : Mor₂) : Mor₂
    - whiskerLeft: (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η : Mor₂) : Mor₂
    - whiskerRight: (e : Expr) (isoLift? : Option IsoLift) (f g : Mor₁) (η : Mor₂) (h : Mor₁) : Mor₂
    - horizontalComp: (e : Expr) (isoLift? : Option IsoLift) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂) : Mor₂
    - coherenceComp: (e : Expr) (isoLift? : Option IsoLift) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂) : Mor₂
    - of: (η : Atom) : Mor₂
-/
inductive Mor₂ : Type where
  /-- The expression for `Iso.hom`. -/
  | isoHom (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  /-- The expression for `Iso.inv`. -/
  | isoInv (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  /-- The expression for the identity `𝟙 f`. -/
  | id (e : Expr) (isoLift : IsoLift) (f : Mor₁) : Mor₂
  /-- The expression for the composition `η ≫ θ`. -/
  | comp (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η θ : Mor₂) : Mor₂
  /-- The expression for the left whiskering `f ◁ η` with `η : g ⟶ h`. -/
  | whiskerLeft (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η : Mor₂) : Mor₂
  /-- The expression for the right whiskering `η ▷ h` with `η : f ⟶ g`. -/
  | whiskerRight (e : Expr) (isoLift? : Option IsoLift) (f g : Mor₁) (η : Mor₂) (h : Mor₁) : Mor₂
  /-- The expression for the horizontal composition `η ◫ θ` with `η : f₁ ⟶ g₁` and `θ : f₂ ⟶ g₂`. -/
  | horizontalComp (e : Expr) (isoLift? : Option IsoLift) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂) : Mor₂
  /-- The expression for the coherence composition `η ⊗≫ θ := η ≫ α ≫ θ` with `η : f ⟶ g`
  and `θ : h ⟶ i`. -/
  | coherenceComp (e : Expr) (isoLift? : Option IsoLift) (f g h i : Mor₁)
    (α : CoherenceHom) (η θ : Mor₂) : Mor₂
  /-- The expression for an atomic non-structural 2-morphism. -/
  | of (η : Atom) : Mor₂
  deriving Inhabited

/--
Definition of `MkMor₂` / `MkMor₂` 的定义

English:
class MkMor₂
  parameters: (m : Type -> Type)
  axioms and operations (1):
    - ofExpr((e : Expr)) : m Mor₂

中文:
类 MkMor₂
  参数: (m : Type -> Type)
  公理与运算 (1 个):
    - ofExpr((e : Expr)) : m Mor₂
-/
class MkMor₂ (m : Type -> Type) where
  /-- Construct a `Mor₂` term from a lean expression. -/
  ofExpr (e : Expr) : m Mor₂

/--
Definition of `Mor₂.e` / `Mor₂.e` 的定义

English:
definition Mor₂.e
  signature: : Mor₂ -> Expr

中文:
定义 Mor₂.e
  签名: : Mor₂ -> Expr
-/
def Mor₂.e : Mor₂ -> Expr
  | .isoHom e .. => e
  | .isoInv e .. => e
  | .id e .. => e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e

/--
Definition of `Mor₂.isoLift?` / `Mor₂.isoLift?` 的定义

English:
definition Mor₂.isoLift?
  signature: : Mor₂ -> Option IsoLift

中文:
定义 Mor₂.isoLift?
  签名: : Mor₂ -> Option IsoLift
-/
def Mor₂.isoLift? : Mor₂ -> Option IsoLift
  | .isoHom _ isoLift .. => some isoLift
  | .isoInv _ isoLift .. => some isoLift
  | .id _ isoLift .. => some isoLift
  | .comp _ isoLift? .. => isoLift?
  | .whiskerLeft _ isoLift? .. => isoLift?
  | .whiskerRight _ isoLift? .. => isoLift?
  | .horizontalComp _ isoLift? .. => isoLift?
  | .coherenceComp _ isoLift? .. => isoLift?
  | .of _ => none

/--
Definition of `Mor₂.srcM` / `Mor₂.srcM` 的定义

English:
definition Mor₂.srcM
  signature: {m : Type -> Type} [Monad m] [MonadMor₁ m]

中文:
定义 Mor₂.srcM
  签名: {m : Type -> Type} [Monad m] [MonadMor₁ m]
-/
def Mor₂.srcM {m : Type -> Type} [Monad m] [MonadMor₁ m] : Mor₂ -> m Mor₁
  | .isoHom _ _ iso => iso.srcM
  | .isoInv _ _ iso => iso.tgtM
  | .id _ _ f => return f
  | .comp _ _ f .. => return f
  | .whiskerLeft _ _ f g .. => do comp₁M f g
  | .whiskerRight _ _ f _ _ h => do comp₁M f h
  | .horizontalComp _ _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .coherenceComp _ _ f .. => return f
  | .of η => return η.src

/--
Definition of `Mor₂.tgtM` / `Mor₂.tgtM` 的定义

English:
definition Mor₂.tgtM
  signature: {m : Type -> Type} [Monad m] [MonadMor₁ m]

中文:
定义 Mor₂.tgtM
  签名: {m : Type -> Type} [Monad m] [MonadMor₁ m]
-/
def Mor₂.tgtM {m : Type -> Type} [Monad m] [MonadMor₁ m] : Mor₂ -> m Mor₁
  | .isoHom _ _ iso => iso.tgtM
  | .isoInv _ _ iso => iso.srcM
  | .id _ _ f => return f
  | .comp _ _ _ _ h .. => return h
  | .whiskerLeft _ _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .coherenceComp _ _ _ _ _ i .. => return i
  | .of η => return η.tgt

/--
Definition of `MonadMor₂` / `MonadMor₂` 的定义

English:
class MonadMor₂
  parameters: (m : Type -> Type)
  axioms and operations (10):
    - homM((η : Mor₂Iso)) : m Mor₂
    - atomHomM((η : AtomIso)) : m Atom
    - invM((η : Mor₂Iso)) : m Mor₂
    - atomInvM((η : AtomIso)) : m Atom
    - id₂M((f : Mor₁)) : m Mor₂
    - comp₂M((η θ : Mor₂)) : m Mor₂
    - whiskerLeftM((f : Mor₁) (η : Mor₂)) : m Mor₂
    - whiskerRightM((η : Mor₂) (h : Mor₁)) : m Mor₂
    - horizontalCompM((η θ : Mor₂)) : m Mor₂
    - coherenceCompM((α : CoherenceHom) (η θ : Mor₂)) : m Mor₂

中文:
类 MonadMor₂
  参数: (m : Type -> Type)
  公理与运算 (10 个):
    - homM((η : Mor₂Iso)) : m Mor₂
    - atomHomM((η : AtomIso)) : m Atom
    - invM((η : Mor₂Iso)) : m Mor₂
    - atomInvM((η : AtomIso)) : m Atom
    - id₂M((f : Mor₁)) : m Mor₂
    - comp₂M((η θ : Mor₂)) : m Mor₂
    - whiskerLeftM((f : Mor₁) (η : Mor₂)) : m Mor₂
    - whiskerRightM((η : Mor₂) (h : Mor₁)) : m Mor₂
    - horizontalCompM((η θ : Mor₂)) : m Mor₂
    - coherenceCompM((α : CoherenceHom) (η θ : Mor₂)) : m Mor₂
-/
class MonadMor₂ (m : Type -> Type) where
  /-- The expression for `Iso.hom η`. -/
  homM (η : Mor₂Iso) : m Mor₂
  /-- The expression for `Iso.hom η`. -/
  atomHomM (η : AtomIso) : m Atom
  /-- The expression for `Iso.inv η`. -/
  invM (η : Mor₂Iso) : m Mor₂
  /-- The expression for `Iso.inv η`. -/
  atomInvM (η : AtomIso) : m Atom
  /-- The expression for the identity `𝟙 f`. -/
  id₂M (f : Mor₁) : m Mor₂
  /-- The expression for the composition `η ≫ θ`. -/
  comp₂M (η θ : Mor₂) : m Mor₂
  /-- The expression for the left whiskering `f ◁ η`. -/
  whiskerLeftM (f : Mor₁) (η : Mor₂) : m Mor₂
  /-- The expression for the right whiskering `η ▷ h`. -/
  whiskerRightM (η : Mor₂) (h : Mor₁) : m Mor₂
  /-- The expression for the horizontal composition `η ◫ θ`. -/
  horizontalCompM (η θ : Mor₂) : m Mor₂
  /-- The expression for the coherence composition `η ⊗≫ θ := η ≫ α ≫ θ`. -/
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂) : m Mor₂

/--
Inductive type `NormalizedHom` / 归纳类型 `NormalizedHom`

English:
inductive NormalizedHom
  parameters: : Type
  constructors (2):
    - nil: (e : Mor₁) (a : Obj) : NormalizedHom
    - cons: (e : Mor₁) : NormalizedHom -> Atom₁ -> NormalizedHom

中文:
归纳类型 NormalizedHom
  参数: : Type
  构造子 (2 个):
    - nil: (e : Mor₁) (a : Obj) : NormalizedHom
    - cons: (e : Mor₁) : NormalizedHom -> Atom₁ -> NormalizedHom
-/
inductive NormalizedHom : Type
  /-- The identity 1-morphism `𝟙 a`. -/
  | nil (e : Mor₁) (a : Obj) : NormalizedHom
  /-- The `cons` composes an atomic 1-morphism at the end of a normalized 1-morphism. -/
  | cons (e : Mor₁) : NormalizedHom -> Atom₁ -> NormalizedHom
  deriving Inhabited

/--
Definition of `NormalizedHom.e` / `NormalizedHom.e` 的定义

English:
definition NormalizedHom.e
  signature: : NormalizedHom -> Mor₁

中文:
定义 NormalizedHom.e
  签名: : NormalizedHom -> Mor₁
-/
def NormalizedHom.e : NormalizedHom -> Mor₁
  | NormalizedHom.nil e _ => e
  | NormalizedHom.cons e _ _ => e

/--
Definition of `NormalizedHom.src` / `NormalizedHom.src` 的定义

English:
definition NormalizedHom.src
  signature: : NormalizedHom -> Obj

中文:
定义 NormalizedHom.src
  签名: : NormalizedHom -> Obj
-/
def NormalizedHom.src : NormalizedHom -> Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ p _ => p.src

/--
Definition of `NormalizedHom.tgt` / `NormalizedHom.tgt` 的定义

English:
definition NormalizedHom.tgt
  signature: : NormalizedHom -> Obj

中文:
定义 NormalizedHom.tgt
  签名: : NormalizedHom -> Obj
-/
def NormalizedHom.tgt : NormalizedHom -> Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ _ f => f.tgt

/--
Definition of `normalizedHom.nilM` / `normalizedHom.nilM` 的定义

English:
definition normalizedHom.nilM
  signature: [MonadMor₁ m] (a : Obj)
  body: do
  return NormalizedHom.nil (← id₁M a) a

中文:
定义 normalizedHom.nilM
  签名: [MonadMor₁ m] (a : Obj)
  定义体: do
  return NormalizedHom.nil (← id₁M a) a
-/
def normalizedHom.nilM [MonadMor₁ m] (a : Obj) : m NormalizedHom := do
  return NormalizedHom.nil (← id₁M a) a

/--
Definition of `NormalizedHom.consM` / `NormalizedHom.consM` 的定义

English:
definition NormalizedHom.consM
  signature: [MonadMor₁ m] (p : NormalizedHom) (f : Atom₁)
  body: do
  return NormalizedHom.cons (← comp₁M p.e (.of f)) p f

中文:
定义 NormalizedHom.consM
  签名: [MonadMor₁ m] (p : NormalizedHom) (f : Atom₁)
  定义体: do
  return NormalizedHom.cons (← comp₁M p.e (.of f)) p f
-/
def NormalizedHom.consM [MonadMor₁ m] (p : NormalizedHom) (f : Atom₁) :
    m NormalizedHom := do
  return NormalizedHom.cons (← comp₁M p.e (.of f)) p f

/--
Definition of `Context` / `Context` 的定义

English:
class Context
  parameters: (ρ : Type)
  axioms and operations (1):
    - mkContext? : Expr -> MetaM (Option ρ)

中文:
类 Context
  参数: (ρ : Type)
  公理与运算 (1 个):
    - mkContext? : Expr -> MetaM (Option ρ)
-/
class Context (ρ : Type) where
  /-- Construct a context from a lean expression for a 2-morphism. -/
  mkContext? : Expr -> MetaM (Option ρ)

export Context (mkContext?)

/--
Definition of `mkContext` / `mkContext` 的定义

English:
definition mkContext
  signature: {ρ : Type} [Context ρ] (e : Expr)
  body: do
  match ← mkContext? e with
  | some c => return c
  | none => throwError "failed to construct a monoidal category or bicategory context from {e}"

中文:
定义 mkContext
  签名: {ρ : Type} [Context ρ] (e : Expr)
  定义体: do
  match ← mkContext? e with
  | some c => return c
  | none => throwError "failed to construct a monoidal category or bicategory context from {e}"
-/
def mkContext {ρ : Type} [Context ρ] (e : Expr) : MetaM ρ := do
  match ← mkContext? e with
  | some c => return c
  | none => throwError "failed to construct a monoidal category or bicategory context from {e}"

/--
Definition of `State` / `State` 的定义

English:
structure State
  parameters: where
  axioms and operations (1):
    - cache : PersistentExprMap Mor₁  [default: {}]

中文:
结构 State
  参数: where
  公理与运算 (1 个):
    - cache : PersistentExprMap Mor₁  [默认: {}]
-/
structure State where
  /-- The cache for evaluating lean expressions of 1-morphisms into `Mor₁` terms. -/
  cache : PersistentExprMap Mor₁ := {}

/--
Definition of `CoherenceM` / `CoherenceM` 的定义

English:
abbreviation CoherenceM
  signature: (ρ : Type)
  body: ReaderT ρ StateT State MetaM

中文:
缩写 CoherenceM
  签名: (ρ : Type)
  定义体: ReaderT ρ StateT State MetaM

Depends on / 依赖: ReaderT, StateT
-/
abbrev CoherenceM (ρ : Type) := ReaderT ρ StateT State MetaM

/--
Definition of `CoherenceM.run` / `CoherenceM.run` 的定义

English:
definition CoherenceM.run
  signature: {α ρ : Type} (x : CoherenceM ρ α) (ctx : ρ) (s : State := {})
  body: do
Prod.fst < > ReaderT.run x ctx s

中文:
定义 CoherenceM.run
  签名: {α ρ : Type} (x : CoherenceM ρ α) (ctx : ρ) (s : State := {})
  定义体: do
Prod.fst < > ReaderT.run x ctx s
-/
def CoherenceM.run {α ρ : Type} (x : CoherenceM ρ α) (ctx : ρ) (s : State := {}) :
    MetaM α := do
Prod.fst < > ReaderT.run x ctx s

end BicategoryLike

end Tactic

end Mathlib
