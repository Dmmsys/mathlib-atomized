/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Ring of integers under a given valuation in a multiplicatively archimedean codomain

-/

public section

section Field

variable {F Γ₀ O : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
  [CommRing O] [Algebra O F] {v : Valuation F Γ₀}

/-
**MonoidWithZeroHom.instLinearOrderedCommGroupWithZeroMrange** 是 Mathlib 中的一个实例，
位于命名空间 ``。
形式化陈述：MonoidWithZeroHom.instLinearOrderedCommGroupWithZeroMrange (v : F ->*₀ Γ₀)
 : LinearOrderedCommGroupWithZero (MonoidHom.mrange v) where bot
参数：v : F ->*₀ Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MonoidWithZeroHom.instLinearOrderedCommGroupWithZeroMrange (v : F →*₀ Γ₀) :
    LinearOrderedCommGroupWithZero (MonoidHom.mrange v) where
  bot := ⟨⊥, by simp [bot_eq_zero]⟩
  bot_le a := by simp [bot_eq_zero, ← Subtype.coe_le_coe]
  isBot_zero a := by simp [← Subtype.coe_le_coe]
  mul_lt_mul_of_pos_left := by
    simp only [← Subtype.coe_lt_coe, val_mrange_zero, Submonoid.coe_mul, Subtype.forall,
      MonoidHom.mem_mrange, forall_exists_index, forall_apply_eq_imp_iff]
    rintro a ha b c hbc
    gcongr
/-
**Valuation.instLinearOrderedCommGroupWithZeroMrange** 是 Mathlib 中的一个实例，位于命名空间 `
`。
形式化陈述：Valuation.instLinearOrderedCommGroupWithZeroMrange : LinearOrderedCommGrou
pWithZero (MonoidHom.mrange v)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Valuation.instLinearOrderedCommGroupWithZeroMrange :
    LinearOrderedCommGroupWithZero (MonoidHom.mrange v) :=
  inferInstanceAs (LinearOrderedCommGroupWithZero (MonoidHom.mrange (.ofClass v : F →*₀ Γ₀)))

namespace Valuation.Integers

open scoped Function in
/-
**Valuation.Integers.wfDvdMonoid_iff_wellFounded_gt_on_v** 是 Mathlib 中的一个引理，位于命名
空间 `Valuation.Integers`。
形式化陈述：wfDvdMonoid_iff_wellFounded_gt_on_v (hv : Integers v O) : WfDvdMonoid O ↔ 
WellFounded ((· > ·) on (v ∘ algebraMap O F))
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.mono`：mono (hr : WellFounded r) (h : forall a b, r' a b -> r
 a b) : WellFounded r'
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Valuation.Integers.dvdNotUnit_iff_lt`：dvdNotUnit_iff_lt (hv : Integers v
 O) {x y : O} : DvdNotUnit x y ↔ v (algebraMap O F y) < v (algebraMap O F x)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma wfDvdMonoid_iff_wellFounded_gt_on_v (hv : Integers v O) :
    WfDvdMonoid O ↔ WellFounded ((· > ·) on (v ∘ algebraMap O F)) := by
  refine ⟨fun _ ↦ wellFounded_dvdNotUnit.mono ?_, fun h ↦ ⟨h.mono ?_⟩⟩ <;>
  simp [Function.onFun, hv.dvdNotUnit_iff_lt]

open scoped Function WithZero in
/-
**Valuation.Integers.wellFounded_gt_on_v_iff_discrete_mrange** 是 Mathlib 中的一个引理，
位于命名空间 `Valuation.Integers`。
形式化陈述：wellFounded_gt_on_v_iff_discrete_mrange [Nontrivial (MonoidHom.mrange v)ˣ]
 (hv : Integers v O) : WellFounded ((· > ·) on (v ∘ algebraMap O F)) ↔ Nonempty 
(MonoidHom.mrange v ≃*o Intᵐ⁰)
参数：MonoidHom.mrange v；hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearOrderedCommGroupWithZero.wellFoundedOn_setOfPred_ge_gt_iff_nonempt
y_discrete_of_ne_zero`：LinearOrderedCommGroupWithZero.wellFoundedOn_setOfPred_ge
_gt_iff_nonempty_discrete_of_ne_zero {G₀ : Type*} [LinearOrderedCommGroupWithZer
o G…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Set.wellFoundedOn_range`：wellFoundedOn_range : (range f).WellFoundedOn r
 ↔ WellFounded (r on f)
· 使用定理 `Set.WellFoundedOn.mono'`：mono' (h : forall (a) (_ : a in s) (b) (_ : b i
n s), r' a b -> r a b) : s.WellFoundedOn r -> s.WellFoundedOn r'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.WellFoundedOn.mapsTo`：∀ {α : Type u_6} {β : Type u_7} {r : α → α → P
rop} (f : β → α) {s : Set α} {t : Set β},   Set.MapsTo f t s → s.WellFoundedOn r
 → t.WellFound…
· 使用定理 `Valuation.Integers.exists_of_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst 
: CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} 
  {O : Type w} [inst_2 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
-/
lemma wellFounded_gt_on_v_iff_discrete_mrange [Nontrivial (MonoidHom.mrange v)ˣ]
    (hv : Integers v O) :
    WellFounded ((· > ·) on (v ∘ algebraMap O F)) ↔
      Nonempty (MonoidHom.mrange v ≃*o ℤᵐ⁰) := by
  rw [←
    LinearOrderedCommGroupWithZero.wellFoundedOn_setOfPred_ge_gt_iff_nonempty_discrete_of_ne_zero
    one_ne_zero, ← Set.wellFoundedOn_range]
  classical
  refine ⟨fun h ↦ (h.mapsTo Subtype.val ?_).mono' (by simp), fun h ↦ (h.mapsTo ?_ ?_).mono' ?_⟩
  · rintro ⟨_, x, rfl⟩
    simp only [← Subtype.coe_le_coe, OneMemClass.coe_one, Set.mem_ofPred_eq, Set.mem_range,
      Function.comp_apply]
    intro hx
    obtain ⟨y, rfl⟩ := hv.exists_of_le_one hx
    exact ⟨y, by simp⟩
  · exact fun x ↦ if hx : x ∈ MonoidHom.mrange v then ⟨x, hx⟩ else 1
  · intro
    simp only [Set.mem_range, Function.comp_apply, MonoidHom.mem_mrange, Set.mem_ofPred_eq,
      forall_exists_index]
    rintro x rfl
    simp [← Subtype.coe_le_coe, hv.map_le_one]
  · simp [Function.onFun]
/-
**Valuation.Integers.isPrincipalIdealRing_iff_not_denselyOrdered** 是 Mathlib 中的一
个引理，位于命名空间 `Valuation.Integers`。
形式化陈述：isPrincipalIdealRing_iff_not_denselyOrdered [MulArchimedean (MonoidHom.mra
nge v)] (hv : Integers v O) : IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (Set.ran
ge v)
参数：MonoidHom.mrange v；hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.Integers.not_denselyOrdered_of_isPrincipalIdealRing`：not_dense
lyOrdered_of_isPrincipalIdealRing [IsPrincipalIdealRing O] (hv : Integers v O) :
 ¬ DenselyOrdered (range v)
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `Valuation.Integers.bijective_algebraMap_of_subsingleton_units_mrange`：bi
jective_algebraMap_of_subsingleton_units_mrange (hv : Integers v O) [Subsingleto
n (MonoidHom.mrange v)ˣ] : Function.Bijective (algebraMap …
· 使用定理 `IsPrincipalIdealRing.of_surjective`：IsPrincipalIdealRing.of_surjective [
IsPrincipalIdealRing R] (f : F) (hf : Function.Surjective f) : IsPrincipalIdealR
ing S
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `ValuationRing.of_integers`：of_integers (v : Valuation K Γ) (hh : v.Integ
ers 𝒪) : haveI
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsBezout.TFAE`：TFAE [IsBezout R] [IsDomain R] : List.TFAE [IsNoetherianR
ing R, IsPrincipalIdealRing R, UniqueFactorizationMonoid R, WfDvdMonoid R]
· 使用定理 `ValuationRing.instIsBezout`：∀ {R : Type u_1} [inst : CommRing R] [inst_1
 : IsDomain R] [ValuationRing R], IsBezout R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.Integers.wfDvdMonoid_iff_wellFounded_gt_on_v`：wfDvdMonoid_iff_
wellFounded_gt_on_v (hv : Integers v O) : WfDvdMonoid O ↔ WellFounded ((· > ·) o
n (v ∘ algebraMap O F))
· 使用引理 `Valuation.Integers.wellFounded_gt_on_v_iff_discrete_mrange`：wellFounded_
gt_on_v_iff_discrete_mrange [Nontrivial (MonoidHom.mrange v)ˣ] (hv : Integers v 
O) : WellFounded ((· > ·) on (v ∘ algebraMap O F…
· 使用引理 `LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered`：LinearOr
deredCommGroupWithZero.discrete_iff_not_denselyOrdered (G : Type*) [LinearOrdere
dCommGroupWithZero G] [Nontrivial Gˣ] [MulArchimedea…
-/
lemma isPrincipalIdealRing_iff_not_denselyOrdered [MulArchimedean (MonoidHom.mrange v)]
    (hv : Integers v O) :
    IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (Set.range v) := by
  refine ⟨fun _ ↦ not_denselyOrdered_of_isPrincipalIdealRing hv, fun H ↦ ?_⟩
  rcases subsingleton_or_nontrivial (MonoidHom.mrange v)ˣ with hs | _
  · have := bijective_algebraMap_of_subsingleton_units_mrange hv
    exact .of_surjective _ (RingEquiv.ofBijective _ this).symm.surjective
  have : IsDomain O := hv.hom_inj.isDomain
  have : ValuationRing O := ValuationRing.of_integers v hv
  have := ((IsBezout.TFAE (R := O)).out 1 3)
  rw [this, hv.wfDvdMonoid_iff_wellFounded_gt_on_v, hv.wellFounded_gt_on_v_iff_discrete_mrange,
    LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered]
  exact H
/-
**Valuation.Integers.isPrincipalIdealRing_iff_not_denselyOrdered_mrange** 是 Math
lib 中的一个引理，位于命名空间 `Valuation.Integers`。
形式化陈述：isPrincipalIdealRing_iff_not_denselyOrdered_mrange [MulArchimedean (Monoid
Hom.mrange v)] (hv : Integers v O) : IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (
MonoidHom.mrange v)
参数：MonoidHom.mrange v；hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.Integers.isPrincipalIdealRing_iff_not_denselyOrdered`：isPrinci
palIdealRing_iff_not_denselyOrdered [MulArchimedean (MonoidHom.mrange v)] (hv : 
Integers v O) : IsPrincipalIdealRing O ↔ ¬ DenselyOr…
-/
lemma isPrincipalIdealRing_iff_not_denselyOrdered_mrange [MulArchimedean (MonoidHom.mrange v)]
    (hv : Integers v O) :
    IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (MonoidHom.mrange v) :=
  isPrincipalIdealRing_iff_not_denselyOrdered hv

end Valuation.Integers

end Field

