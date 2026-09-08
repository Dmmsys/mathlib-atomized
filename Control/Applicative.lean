/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Control.Functor
public import Mathlib.Control.Basic

import Mathlib.Tactic.Attr.Register

/-!
# `applicative` instances

This file provides `Applicative` instances for concrete functors:
* `id`
* `Functor.comp`
* `Functor.const`
* `Functor.add_const`
-/

public section

universe u v w

section Lemmas

open Function

variable {F : Type u → Type v}
variable [Applicative F] [LawfulApplicative F]
variable {α β γ σ : Type u}

/-
**Applicative.map_seq_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Applicative.map_seq_map (f : α -> β -> γ) (g : σ -> β) (x : F α) (y : F σ)
 : f < > x <*> g < > y = ((· ∘ g) ∘ f) < > x <*> y
参数：f : α -> β -> γ；g : σ -> β；x : F α；y : F σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `seq_map_assoc`：seq_map_assoc (x : F (α -> β)) (f : γ -> α) (y : F γ) : x
 <*> f < > y = (· ∘ f) < > x <*> y
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Applicative.map_seq_map (f : α → β → γ) (g : σ → β) (x : F α) (y : F σ) :
    f <$> x <*> g <$> y = ((· ∘ g) ∘ f) <$> x <*> y := by
  simp [functor_norm, Function.comp_def]
/-
**Applicative.pure_seq_eq_map'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Applicative.pure_seq_eq_map' (f : α -> β) : ((pure f : F (α -> β)) <*> ·) 
= (f <$> ·)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.pure_seq`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : f α),   pure g <
*> x = g <$> x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Applicative.pure_seq_eq_map' (f : α → β) : ((pure f : F (α → β)) <*> ·) = (f <$> ·) := by
  simp [functor_norm]

set_option linter.overlappingInstances false in
/-
**Applicative.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Applicative.ext {F} : forall {A1 : Applicative F} {A2 : Applicative F} [@L
awfulApplicative F A1] [@LawfulApplicative F A2], (forall {α : Type u} (x : α), 
@Pure.pure _ A1.toPure _ x = @Pure.pure _ A2.toPure _ x) -> (forall {α β : Type 
u} (f : F (α -> β)) (x : F α), @Seq.seq _ A1.toSeq _ _ f (fun _ => x) = @Seq.seq
 _ A2.toSeq _ _ f (fun _ => x)) -> A1 = A2 | { toFunctor
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Functor.ext`：Functor.ext {F} : forall {F1 : Functor F} {F2 : Functor F} 
[@LawfulFunctor F F1] [@LawfulFunctor F F2], (forall (α β) (f : α -> β) (x : F α
)…
-/
theorem Applicative.ext {F} :
    ∀ {A1 : Applicative F} {A2 : Applicative F} [@LawfulApplicative F A1] [@LawfulApplicative F A2],
      (∀ {α : Type u} (x : α), @Pure.pure _ A1.toPure _ x = @Pure.pure _ A2.toPure _ x) →
      (∀ {α β : Type u} (f : F (α → β)) (x : F α),
          @Seq.seq _ A1.toSeq _ _ f (fun _ => x) = @Seq.seq _ A2.toSeq _ _ f (fun _ => x)) →
      A1 = A2
  | { toFunctor := F1, seq := s1, pure := p1, seqLeft := sl1, seqRight := sr1 },
    { toFunctor := F2, seq := s2, pure := p2, seqLeft := sl2, seqRight := sr2 },
    L1, L2, H1, H2 => by
    obtain rfl : @p1 = @p2 := by
      funext α x
      apply H1
    obtain rfl : @s1 = @s2 := by
      funext α β f x
      exact H2 f (x Unit.unit)
    obtain ⟨seqLeft_eq1, seqRight_eq1, pure_seq1, -⟩ := L1
    obtain ⟨seqLeft_eq2, seqRight_eq2, pure_seq2, -⟩ := L2
    obtain rfl : F1 = F2 := by
      apply Functor.ext
      intros
      exact (pure_seq1 _ _).symm.trans (pure_seq2 _ _)
    congr <;> funext α β x y
    · exact (seqLeft_eq1 _ (y Unit.unit)).trans (seqLeft_eq2 _ _).symm
    · exact (seqRight_eq1 _ (y Unit.unit)).trans (seqRight_eq2 _ (y Unit.unit)).symm

end Lemmas

-- Porting note: we have a monad instance for `Id` but not `id`, mathport can't tell
-- which one is intended

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommApplicative Id where commutative_prod _ _ := rfl

namespace Functor

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u → Type w} {G : Type v → Type u}
variable [Applicative F] [Applicative G]
variable [LawfulApplicative F] [LawfulApplicative G]
variable {α β γ : Type v}

/-
**Functor.Comp.map_pure** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：map_pure (f : α -> β) (x : α) : (f <$> pure x : Comp F G β) = pure (f x)
参数：f : α -> β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Functor.Comp.ext`：∀ {F : Type u → Type w} {G : Type v → Type u} {α : Typ
e v} {x y : Functor.Comp F G α}, x.run = y.run → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Functor.Comp.run_pure`：∀ {F : Type u → Type w} {G : Type v → Type u} [in
st : Applicative F] [inst_1 : Applicative G] {α : Type v} (x : α),   (pure x).ru
n = pure (p…
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_pure (f : α → β) (x : α) : (f <$> pure x : Comp F G β) = pure (f x) :=
  Comp.ext <| by simp
/-
**Functor.Comp.seq_pure** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：seq_pure (f : Comp F G (α -> β)) (x : α) : f <*> pure x = (fun g : α -> β 
=> g x) < > f
参数：f : Comp F G (α -> β)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Functor.Comp.ext`：∀ {F : Type u → Type w} {G : Type v → Type u} {α : Typ
e v} {x y : Functor.Comp F G α}, x.run = y.run → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Functor.Comp.run_pure`：∀ {F : Type u → Type w} {G : Type v → Type u} [in
st : Applicative F] [inst_1 : Applicative G] {α : Type v} (x : α),   (pure x).ru
n = pure (p…
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem seq_pure (f : Comp F G (α → β)) (x : α) : f <*> pure x = (fun g : α → β => g x) <$> f :=
  Comp.ext <| by simp [functor_norm]
/-
**Functor.Comp.seq_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：seq_assoc (x : Comp F G α) (f : Comp F G (α -> β)) (g : Comp F G (β -> γ))
 : g <*> (f <*> x) = @Function.comp α β γ < > g <*> f <*> x
参数：x : Comp F G α；f : Comp F G (α -> β)；g : Comp F G (β -> γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Functor.Comp.ext`：∀ {F : Type u → Type w} {G : Type v → Type u} {α : Typ
e v} {x y : Functor.Comp F G α}, x.run = y.run → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.seq_assoc`：∀ {f : Type u → Type v} {inst : Applicative
 f} [self : LawfulApplicative f] {α β γ : Type u} (x : f α) (g : f (α → β))   (h
 : f (β → γ)), h …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `seq_map_assoc`：seq_map_assoc (x : F (α -> β)) (f : γ -> α) (y : F γ) : x
 <*> f < > y = (· ∘ f) < > x <*> y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_seq`：map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) : f < > (x <*> 
y) = (f ∘ ·) < > x <*> y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem seq_assoc (x : Comp F G α) (f : Comp F G (α → β)) (g : Comp F G (β → γ)) :
    g <*> (f <*> x) = @Function.comp α β γ <$> g <*> f <*> x :=
  Comp.ext <| by simp [comp_def, functor_norm]
/-
**Functor.Comp.pure_seq_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：pure_seq_eq_map (f : α -> β) (x : Comp F G α) : pure f <*> x = f < > x
参数：f : α -> β；x : Comp F G α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Functor.Comp.ext`：∀ {F : Type u → Type w} {G : Type v → Type u} {α : Typ
e v} {x y : Functor.Comp F G α}, x.run = y.run → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Functor.Comp.run_pure`：∀ {F : Type u → Type w} {G : Type v → Type u} [in
st : Applicative F] [inst_1 : Applicative G] {α : Type v} (x : α),   (pure x).ru
n = pure (p…
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.pure_seq`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : f α),   pure g <
*> x = g <$> x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pure_seq_eq_map (f : α → β) (x : Comp F G α) : pure f <*> x = f <$> x :=
  Comp.ext <| by simp [functor_norm]

-- TODO: the first two results were handled by `control_laws_tac` in mathlib3
/-
**Functor.Comp.instLawfulApplicativeComp** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp
`。
形式化陈述：instLawfulApplicativeComp : LawfulApplicative (Comp F G) where seqLeft_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `Functor.Comp.pure_seq_eq_map`：pure_seq_eq_map (f : α -> β) (x : Comp F G
 α) : pure f <*> x = f < > x
· 使用定理 `Functor.Comp.map_pure`：map_pure (f : α -> β) (x : α) : (f <$> pure x : C
omp F G β) = pure (f x)
· 使用定理 `Functor.Comp.seq_pure`：seq_pure (f : Comp F G (α -> β)) (x : α) : f <*> 
pure x = (fun g : α -> β => g x) < > f
· 使用定理 `Functor.Comp.seq_assoc`：seq_assoc (x : Comp F G α) (f : Comp F G (α -> β
)) (g : Comp F G (β -> γ)) : g <*> (f <*> x) = @Function.comp α β γ < > g <*> f 
<*> x
-/
instance instLawfulApplicativeComp : LawfulApplicative (Comp F G) where
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := Comp.pure_seq_eq_map
  map_pure := Comp.map_pure
  seq_pure := Comp.seq_pure
  seq_assoc := Comp.seq_assoc
/-
**Functor.Comp.applicative_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：applicative_id_comp {F} [AF : Applicative F] [LawfulApplicative F] : @inst
ApplicativeComp Id F _ _ = AF
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Applicative.ext`：Applicative.ext {F} : forall {A1 : Applicative F} {A2 :
 Applicative F} [@LawfulApplicative F A1] [@LawfulApplicative F A2], (forall {α 
: Typ…
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
-/
theorem applicative_id_comp {F} [AF : Applicative F] [LawfulApplicative F] :
    @instApplicativeComp Id F _ _ = AF :=
  @Applicative.ext F _ _ (instLawfulApplicativeComp (F := Id)) _
    (fun _ => rfl) (fun _ _ => rfl)
/-
**Functor.Comp.applicative_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：applicative_comp_id {F} [AF : Applicative F] [LawfulApplicative F] : @Comp
.instApplicativeComp F Id _ _ = AF
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Applicative.ext`：Applicative.ext {F} : forall {A1 : Applicative F} {A2 :
 Applicative F} [@LawfulApplicative F A1] [@LawfulApplicative F A2], (forall {α 
: Typ…
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
-/
theorem applicative_comp_id {F} [AF : Applicative F] [LawfulApplicative F] :
    @Comp.instApplicativeComp F Id _ _ = AF :=
  @Applicative.ext F _ _ (instLawfulApplicativeComp (G := Id)) _
    (fun _ => rfl) (fun f x => show id <$> f <*> x = f <*> x by rw [id_map])

open CommApplicative

set_option backward.isDefEq.respectTransparency false in
/-
**Functor.Comp.** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : Type u → Type w} {g : Type v → Type u} [Applicative f] [Applicative g]
    [CommApplicative f] [CommApplicative g] : CommApplicative (Comp f g) where
  commutative_prod _ _ := by
    simp! [map, Seq.seq]
    rw [commutative_map]
    simp only [mk, flip, seq_map_assoc, Function.comp_def, map_map]
    congr
    funext x y
    rw [commutative_map]
    congr

end Comp

end Functor

open Functor

@[functor_norm]
/-
**Comp.seq_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Comp.seq_mk {α β : Type w} {f : Type u -> Type v} {g : Type w -> Type u} [
Applicative f] [Applicative g] (h : f (g (α -> β))) (x : f (g α)) : Comp.mk h <*
> Comp.mk x = Comp.mk ((· <*> ·) <$> h <*> x)
参数：h : f (g (α -> β))；x : f (g α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Comp.seq_mk {α β : Type w} {f : Type u → Type v} {g : Type w → Type u} [Applicative f]
    [Applicative g] (h : f (g (α → β))) (x : f (g α)) :
    Comp.mk h <*> Comp.mk x = Comp.mk ((· <*> ·) <$> h <*> x) :=
  rfl

-- Porting note: There is some awkwardness in the following definition now that we have `HMul`.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [One α] [Mul α] : Applicative (Const α) where
  pure _ := (1 : α)
  seq f x := (show α from f) * (show α from x Unit.unit)

-- Porting note: `(· <*> ·)` needed to change to `Seq.seq` in the `simp`.
-- Also, `simp` didn't close `refl` goals.

set_option backward.isDefEq.respectTransparency false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [Monoid α] : LawfulApplicative (Const α) where
  map_pure _ _ := rfl
  seq_pure _ _ := by simp [Const.map, map, Seq.seq, pure, mul_one]
  pure_seq _ _ := by simp [Const.map, map, Seq.seq, pure, one_mul]
  seqLeft_eq _ _ := by simp [Seq.seq, SeqLeft.seqLeft]
  seqRight_eq _ _ := by simp [Seq.seq, SeqRight.seqRight]
  seq_assoc _ _ _ := by simp [Const.map, map, Seq.seq, mul_assoc]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [Zero α] [Add α] : Applicative (AddConst α) where
  pure _ := (0 : α)
  seq f x := (show α from f) + (show α from x Unit.unit)

set_option backward.isDefEq.respectTransparency false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [AddMonoid α] : LawfulApplicative (AddConst α) where
  map_pure _ _ := rfl
  seq_pure _ _ := by simp [Const.map, map, Seq.seq, pure, add_zero]
  pure_seq _ _ := by simp [Const.map, map, Seq.seq, pure, zero_add]
  seqLeft_eq _ _ := by simp [Seq.seq, SeqLeft.seqLeft]
  seqRight_eq _ _ := by simp [Seq.seq, SeqRight.seqRight]
  seq_assoc _ _ _ := by simp [Const.map, map, Seq.seq, add_assoc]
