/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.Algebra.Lie.Quotient

/-!
# The normalizer of Lie submodules and subalgebras.

Given a Lie module `M` over a Lie subalgebra `L`, the normalizer of a Lie submodule `N ⊆ M` is
the Lie submodule with underlying set `{ m | ∀ (x : L), ⁅x, m⁆ ∈ N }`.

The lattice of Lie submodules thus has two natural operations, the normalizer: `N ↦ N.normalizer`
and the ideal operation: `N ↦ ⁅⊤, N⁆`; these are adjoint, i.e., they form a Galois connection. This
adjointness is the reason that we may define nilpotency in terms of either the upper or lower
central series.

Given a Lie subalgebra `H ⊆ L`, we may regard `H` as a Lie submodule of `L` over `H`, and thus
consider the normalizer. This turns out to be a Lie subalgebra.

## Main definitions

  * `LieSubmodule.normalizer`
  * `LieSubalgebra.normalizer`
  * `LieSubmodule.gc_top_lie_normalizer`

## Tags

lie algebra, normalizer
-/

@[expose] public section


variable {R L M M' : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

/--
Definition of `normalizer` / `normalizer` 的定义

English:
definition normalizer
  signature: : LieSubmodule R L M where
  body: {m | forall x : L, ⁅x, m⁆ in N}
  add_mem' hm₁ hm₂ x := by rw [lie_add]; exact N.add_mem' (hm₁ x) (hm₂ x)
  zero_mem' x := by simp
  smul_mem' t m hm x := by rw [lie_smul]; exact N.smul_mem' t (hm x)
  lie_mem {x m} hm y := by rw [leibniz_lie]; exact N.add_mem' (hm ⁅y, x⁆) (N.lie_mem (hm y))

@[simp]

中文:
定义 normalizer
  签名: : Lie子模 R L M where
  定义体: {m | forall x : L, ⁅x, m⁆ in N}
  add_mem' hm₁ hm₂ x := by rw [lie_add]; exact N.add_mem' (hm₁ x) (hm₂ x)
  zero_mem' x := by simp
  smul_mem' t m hm x := by rw [lie_smul]; exact N.smul_mem' t (hm x)
  lie_mem {x m} hm y := by rw [leibniz_lie]; exact N.add_mem' (hm ⁅y, x⁆) (N.lie_mem (hm y))

@[simp]
-/
def normalizer : LieSubmodule R L M where
  carrier := {m | forall x : L, ⁅x, m⁆ in N}
  add_mem' hm₁ hm₂ x := by rw [lie_add]; exact N.add_mem' (hm₁ x) (hm₂ x)
  zero_mem' x := by simp
  smul_mem' t m hm x := by rw [lie_smul]; exact N.smul_mem' t (hm x)
  lie_mem {x m} hm y := by rw [leibniz_lie]; exact N.add_mem' (hm ⁅y, x⁆) (N.lie_mem (hm y))

@[simp]
/--
theorem `mem_normalizer` / 定理 `mem_normalizer`

English:
theorem mem_normalizer
  given: (m : M)
  statement: m in N.normalizer ↔ forall x : L, ⁅x, m⁆ in N
  proof: Iff.rfl

@[simp]

中文:
定理 mem_normalizer
  条件: (m : M)
  结论: m in N.normalizer ↔ 对任意 x : L, ⁅x, m⁆ in N
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_normalizer (m : M) : m in N.normalizer ↔ forall x : L, ⁅x, m⁆ in N :=
  Iff.rfl

@[simp]
/--
theorem `le_normalizer` / 定理 `le_normalizer`

English:
theorem le_normalizer
  statement: N <= N.normalizer
  proof: by
  intro m hm
  rw [mem_normalizer]
  exact fun x => N.lie_mem hm

中文:
定理 le_normalizer
  结论: N <= N.normalizer
  证明: by
  intro m hm
  rw [mem_normalizer]
  exact fun x => N.lie_mem hm

Depends on / 依赖: N.lie_mem, lie_mem, mem_normalizer
-/
theorem le_normalizer : N <= N.normalizer := by
  intro m hm
  rw [mem_normalizer]
  exact fun x => N.lie_mem hm

/--
theorem `normalizer_inf` / 定理 `normalizer_inf`

English:
theorem normalizer_inf
  statement: (N₁ ⊓ N₂).normalizer = N₁.normalizer ⊓ N₂.normalizer
  proof: by
  ext; simp [← forall_and]

@[gcongr, mono]

中文:
定理 normalizer_inf
  结论: (N₁ ⊓ N₂).normalizer = N₁.normalizer ⊓ N₂.normalizer
  证明: by
  ext; simp [← forall_and]

@[gcongr, mono]

Depends on / 依赖: forall_and
-/
theorem normalizer_inf : (N₁ ⊓ N₂).normalizer = N₁.normalizer ⊓ N₂.normalizer := by
  ext; simp [← forall_and]

@[gcongr, mono]
/--
theorem `normalizer_mono` / 定理 `normalizer_mono`

English:
theorem normalizer_mono
  given: (h : N₁ <= N₂)
  statement: normalizer N₁ <= normalizer N₂
  proof: by
  intro m hm
  rw [mem_normalizer] at hm ⊢
  exact fun x => h (hm x)

中文:
定理 normalizer_mono
  条件: (h : N₁ <= N₂)
  结论: normalizer N₁ <= normalizer N₂
  证明: by
  intro m hm
  rw [mem_normalizer] at hm ⊢
  exact fun x => h (hm x)

Depends on / 依赖: mem_normalizer
-/
theorem normalizer_mono (h : N₁ <= N₂) : normalizer N₁ <= normalizer N₂ := by
  intro m hm
  rw [mem_normalizer] at hm ⊢
  exact fun x => h (hm x)

/--
theorem `monotone_normalizer` / 定理 `monotone_normalizer`

English:
theorem monotone_normalizer
  statement: Monotone (normalizer : LieSubmodule R L M -> LieSubmodule R L M)
  proof: fun _ _ => normalizer_mono

@[simp]

中文:
定理 monotone_normalizer
  结论: 递增 (normalizer : Lie子模 R L M -> Lie子模 R L M)
  证明: fun _ _ => normalizer_mono

@[simp]

Depends on / 依赖: normalizer_mono
-/
theorem monotone_normalizer : Monotone (normalizer : LieSubmodule R L M -> LieSubmodule R L M) :=
  fun _ _ => normalizer_mono

@[simp]
/--
theorem `comap_normalizer` / 定理 `comap_normalizer`

English:
theorem comap_normalizer
  given: (f : M' ->ₗ⁅R,L⁆ M)
  statement: N.normalizer.comap f = (N.comap f).normalizer
  proof: by
  ext; simp

中文:
定理 comap_normalizer
  条件: (f : M' ->ₗ⁅R,L⁆ M)
  结论: N.normalizer.comap f = (N.comap f).normalizer
  证明: by
  ext; simp
-/
theorem comap_normalizer (f : M' ->ₗ⁅R,L⁆ M) : N.normalizer.comap f = (N.comap f).normalizer := by
  ext; simp

/--
theorem `top_lie_le_iff_le_normalizer` / 定理 `top_lie_le_iff_le_normalizer`

English:
theorem top_lie_le_iff_le_normalizer
  given: (N' : LieSubmodule R L M)
  proof: by rw [lie_le_iff]; tauto

中文:
定理 top_lie_le_iff_le_normalizer
  条件: (N' : Lie子模 R L M)
  证明: by rw [lie_le_iff]; tauto

Depends on / 依赖: lie_le_iff
-/
theorem top_lie_le_iff_le_normalizer (N' : LieSubmodule R L M) :
    ⁅(⊤ : LieIdeal R L), N⁆ <= N' ↔ N <= N'.normalizer := by rw [lie_le_iff]; tauto

/--
theorem `gc_top_lie_normalizer` / 定理 `gc_top_lie_normalizer`

English:
theorem gc_top_lie_normalizer
  proof: top_lie_le_iff_le_normalizer

中文:
定理 gc_top_lie_normalizer
  证明: top_lie_le_iff_le_normalizer

Depends on / 依赖: top_lie_le_iff_le_normalizer
-/
theorem gc_top_lie_normalizer :
    GaloisConnection (fun N : LieSubmodule R L M => ⁅(⊤ : LieIdeal R L), N⁆) normalizer :=
  top_lie_le_iff_le_normalizer

variable (R L M) in
/--
theorem `normalizer_bot_eq_maxTrivSubmodule` / 定理 `normalizer_bot_eq_maxTrivSubmodule`

English:
theorem normalizer_bot_eq_maxTrivSubmodule
  proof: rfl

中文:
定理 normalizer_bot_eq_maxTrivSubmodule
  证明: rfl
-/
theorem normalizer_bot_eq_maxTrivSubmodule :
    (⊥ : LieSubmodule R L M).normalizer = LieModule.maxTrivSubmodule R L M :=
  rfl

/--
Definition of `idealizer` / `idealizer` 的定义

English:
definition idealizer
  signature: : LieIdeal R L where
  body: {x : L | forall m : M, ⁅x, m⁆ in N}
  add_mem' := fun {x} {y} hx hy m => by rw [add_lie]; exact N.add_mem (hx m) (hy m)
  zero_mem' := by simp
  smul_mem' := fun t {x} hx m => by rw [smul_lie]; exact N.smul_mem t (hx m)
  lie_mem := fun {x} {y} hy m => by rw [lie_lie]; exact sub_mem (N.lie_mem (hy m)) (hy ⁅x, m⁆)

@[simp]

中文:
定义 idealizer
  签名: : LieIdeal R L where
  定义体: {x : L | forall m : M, ⁅x, m⁆ in N}
  add_mem' := fun {x} {y} hx hy m => by rw [add_lie]; exact N.add_mem (hx m) (hy m)
  zero_mem' := by simp
  smul_mem' := fun t {x} hx m => by rw [smul_lie]; exact N.smul_mem t (hx m)
  lie_mem := fun {x} {y} hy m => by rw [lie_lie]; exact sub_mem (N.lie_mem (hy m)) (hy ⁅x, m⁆)

@[simp]
-/
def idealizer : LieIdeal R L where
  carrier := {x : L | forall m : M, ⁅x, m⁆ in N}
  add_mem' := fun {x} {y} hx hy m => by rw [add_lie]; exact N.add_mem (hx m) (hy m)
  zero_mem' := by simp
  smul_mem' := fun t {x} hx m => by rw [smul_lie]; exact N.smul_mem t (hx m)
  lie_mem := fun {x} {y} hy m => by rw [lie_lie]; exact sub_mem (N.lie_mem (hy m)) (hy ⁅x, m⁆)

@[simp]
/--
lemma `mem_idealizer` / 引理 `mem_idealizer`

English:
lemma mem_idealizer
  given: {x : L}
  statement: x in N.idealizer ↔ forall m : M, ⁅x, m⁆ in N
  proof: Iff.rfl

@[simp]

中文:
引理 mem_idealizer
  条件: {x : L}
  结论: x in N.idealizer ↔ 对任意 m : M, ⁅x, m⁆ in N
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_idealizer {x : L} : x in N.idealizer ↔ forall m : M, ⁅x, m⁆ in N := Iff.rfl

@[simp]
/--
lemma `_root_.LieIdeal.idealizer_eq_normalizer` / 引理 `_root_.LieIdeal.idealizer_eq_normalizer`

English:
lemma _root_.LieIdeal.idealizer_eq_normalizer
  given: (I : LieIdeal R L)
  proof: by
  ext x; exact forall_congr' fun y => by simp only [← lie_skew x y, neg_mem_iff]

中文:
引理 _root_.LieIdeal.idealizer_eq_normalizer
  条件: (I : LieIdeal R L)
  证明: by
  ext x; exact forall_congr' fun y => by simp only [← lie_skew x y, neg_mem_iff]

Depends on / 依赖: forall_congr, lie_skew, neg_mem_iff
-/
lemma _root_.LieIdeal.idealizer_eq_normalizer (I : LieIdeal R L) :
    I.idealizer = I.normalizer := by
  ext x; exact forall_congr' fun y => by simp only [← lie_skew x y, neg_mem_iff]

end LieSubmodule

namespace LieSubalgebra

variable (H : LieSubalgebra R L)

/--
Definition of `normalizer` / `normalizer` 的定义

English:
definition normalizer
  signature: : LieSubalgebra R L
  body: { H.toLieSubmodule.normalizer with
    lie_mem' := fun {y z} hy hz x => by
      rw [coe_bracket_of_module]; rw [mem_toLieSubmodule]; rw [leibniz_lie]; rw [← lie_skew y]; rw [← sub_eq_add_neg]
      exact H.sub_mem (hz ⟨_, hy x⟩) (hy ⟨_, hz x⟩) }

中文:
定义 normalizer
  签名: : Lie子代数 R L
  定义体: { H.toLieSubmodule.normalizer with
    lie_mem' := fun {y z} hy hz x => by
      rw [coe_bracket_of_module]; rw [mem_toLieSubmodule]; rw [leibniz_lie]; rw [← lie_skew y]; rw [← sub_eq_add_neg]
      exact H.sub_mem (hz ⟨_, hy x⟩) (hy ⟨_, hz x⟩) }

Depends on / 依赖: H.sub_mem, H.toLieSubmodule.normalizer, coe_bracket_of_module, leibniz_lie, lie_mem, lie_skew, mem_toLieSubmodule, normalizer, sub_eq_add_neg, sub_mem, toLieSubmodule
-/
def normalizer : LieSubalgebra R L :=
  { H.toLieSubmodule.normalizer with
    lie_mem' := fun {y z} hy hz x => by
      rw [coe_bracket_of_module]; rw [mem_toLieSubmodule]; rw [leibniz_lie]; rw [← lie_skew y]; rw [← sub_eq_add_neg]
      exact H.sub_mem (hz ⟨_, hy x⟩) (hy ⟨_, hz x⟩) }

/--
theorem `mem_normalizer_iff'` / 定理 `mem_normalizer_iff'`

English:
theorem mem_normalizer_iff'
  given: (x : L)
  statement: x in H.normalizer ↔ forall y : L, y in H -> ⁅y, x⁆ in H
  proof: by
  rw [Subtype.forall']; rfl

中文:
定理 mem_normalizer_iff'
  条件: (x : L)
  结论: x in H.normalizer ↔ 对任意 y : L, y in H -> ⁅y, x⁆ in H
  证明: by
  rw [Subtype.forall']; rfl

Depends on / 依赖: Subtype, Subtype.forall
-/
theorem mem_normalizer_iff' (x : L) : x in H.normalizer ↔ forall y : L, y in H -> ⁅y, x⁆ in H := by
  rw [Subtype.forall']; rfl

/--
theorem `mem_normalizer_iff` / 定理 `mem_normalizer_iff`

English:
theorem mem_normalizer_iff
  given: (x : L)
  statement: x in H.normalizer ↔ forall y : L, y in H -> ⁅x, y⁆ in H
  proof: by
  rw [mem_normalizer_iff']
  refine forall₂_congr fun y hy => ?_
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]

中文:
定理 mem_normalizer_iff
  条件: (x : L)
  结论: x in H.normalizer ↔ 对任意 y : L, y in H -> ⁅x, y⁆ in H
  证明: by
  rw [mem_normalizer_iff']
  refine forall₂_congr fun y hy => ?_
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]

Depends on / 依赖: lie_skew, mem_normalizer_iff, neg_mem_iff
-/
theorem mem_normalizer_iff (x : L) : x in H.normalizer ↔ forall y : L, y in H -> ⁅x, y⁆ in H := by
  rw [mem_normalizer_iff']
  refine forall₂_congr fun y hy => ?_
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]

/--
theorem `le_normalizer` / 定理 `le_normalizer`

English:
theorem le_normalizer
  statement: H <= H.normalizer
  proof: H.toLieSubmodule.le_normalizer

中文:
定理 le_normalizer
  结论: H <= H.normalizer
  证明: H.toLieSubmodule.le_normalizer

Depends on / 依赖: H.toLieSubmodule.le_normalizer, le_normalizer, toLieSubmodule
-/
theorem le_normalizer : H <= H.normalizer :=
  H.toLieSubmodule.le_normalizer

/--
theorem `coe_normalizer_eq_normalizer` / 定理 `coe_normalizer_eq_normalizer`

English:
theorem coe_normalizer_eq_normalizer
  proof: rfl

中文:
定理 coe_normalizer_eq_normalizer
  证明: rfl
-/
theorem coe_normalizer_eq_normalizer :
    (H.toLieSubmodule.normalizer : Submodule R L) = H.normalizer :=
  rfl

variable {H}

/--
theorem `lie_mem_sup_of_mem_normalizer` / 定理 `lie_mem_sup_of_mem_normalizer`

English:
theorem lie_mem_sup_of_mem_normalizer
  statement: {x y z : L} (hx : x in H.normalizer) (hy : y in R ∙ x ⊔ ↑H)
  proof: by
  rw [Submodule.mem_sup] at hy hz
  obtain ⟨u₁, hu₁, v, hv : v in H, rfl⟩ := hy
  obtain ⟨u₂, hu₂, w, hw : w in H, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
  apply Submodule.mem_sup_right
  simp only [LieSubalgebra.mem_toSubmodule, smul_lie, add_lie, zero_add, lie_add, smul_zero,
    lie_smul, lie_self]
  refine H.add_mem (H.smul_mem s ?_) (H.add_mem (H.smul_mem t ?_) (H.lie_mem hv hw))
  exacts [(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]

中文:
定理 lie_mem_sup_of_mem_normalizer
  结论: {x y z : L} (hx : x in H.normalizer) (hy : y in R ∙ x ⊔ ↑H)
  证明: by
  rw [Submodule.mem_sup] at hy hz
  obtain ⟨u₁, hu₁, v, hv : v in H, rfl⟩ := hy
  obtain ⟨u₂, hu₂, w, hw : w in H, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
  apply Submodule.mem_sup_right
  simp only [LieSubalgebra.mem_toSubmodule, smul_lie, add_lie, zero_add, lie_add, smul_zero,
    lie_smul, lie_self]
  refine H.add_mem (H.smul_mem s ?_) (H.add_mem (H.smul_mem t ?_) (H.lie_mem hv hw))
  exacts [(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]

Depends on / 依赖: H.add_mem, H.lie_mem, H.mem_normalizer_iff, H.smul_mem, LieSubalgebra, LieSubalgebra.mem_toSubmodule, Submodule, Submodule.mem_span_singleton.mp, Submodule.mem_sup, Submodule.mem_sup_right, add_lie, add_mem, exacts, lie_add, lie_mem, lie_self, lie_smul, mem_normalizer_iff, mem_span_singleton, mem_sup
-/
theorem lie_mem_sup_of_mem_normalizer {x y z : L} (hx : x in H.normalizer) (hy : y in R ∙ x ⊔ ↑H)
    (hz : z in R ∙ x ⊔ ↑H) : ⁅y, z⁆ in R ∙ x ⊔ ↑H := by
  rw [Submodule.mem_sup] at hy hz
  obtain ⟨u₁, hu₁, v, hv : v in H, rfl⟩ := hy
  obtain ⟨u₂, hu₂, w, hw : w in H, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
  apply Submodule.mem_sup_right
  simp only [LieSubalgebra.mem_toSubmodule, smul_lie, add_lie, zero_add, lie_add, smul_zero,
    lie_smul, lie_self]
  refine H.add_mem (H.smul_mem s ?_) (H.add_mem (H.smul_mem t ?_) (H.lie_mem hv hw))
  exacts [(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]

/--
theorem `ideal_in_normalizer` / 定理 `ideal_in_normalizer`

English:
theorem ideal_in_normalizer
  given: {x y : L} (hx : x in H.normalizer) (hy : y in H)
  statement: ⁅x, y⁆ in H
  proof: by
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]
  exact hx ⟨y, hy⟩

中文:
定理 ideal_in_normalizer
  条件: {x y : L} (hx : x in H.normalizer) (hy : y in H)
  结论: ⁅x, y⁆ in H
  证明: by
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]
  exact hx ⟨y, hy⟩

Depends on / 依赖: lie_skew, neg_mem_iff
-/
theorem ideal_in_normalizer {x y : L} (hx : x in H.normalizer) (hy : y in H) : ⁅x, y⁆ in H := by
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]
  exact hx ⟨y, hy⟩

/--
theorem `exists_nested_lieIdeal_ofLe_normalizer` / 定理 `exists_nested_lieIdeal_ofLe_normalizer`

English:
theorem exists_nested_lieIdeal_ofLe_normalizer
  statement: {K : LieSubalgebra R L} (h₁ : H <= K)
  proof: by
  rw [exists_nested_lieIdeal_coe_eq_iff]
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy

中文:
定理 存在_nested_lieIdeal_ofLe_normalizer
  结论: {K : Lie子代数 R L} (h₁ : H <= K)
  证明: by
  rw [exists_nested_lieIdeal_coe_eq_iff]
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy

Depends on / 依赖: exists_nested_lieIdeal_coe_eq_iff, ideal_in_normalizer
-/
theorem exists_nested_lieIdeal_ofLe_normalizer {K : LieSubalgebra R L} (h₁ : H <= K)
    (h₂ : K <= H.normalizer) : exists I : LieIdeal R K, (I : LieSubalgebra R K) = ofLe h₁ := by
  rw [exists_nested_lieIdeal_coe_eq_iff]
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy

variable (H)

/--
theorem `normalizer_eq_self_iff` / 定理 `normalizer_eq_self_iff`

English:
theorem normalizer_eq_self_iff
  proof: by
  rw [LieSubmodule.eq_bot_iff]
  refine ⟨fun h => ?_, fun h => le_antisymm ?_ H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x in H by rwa [Submodule.Quotient.quot_mk_eq_mk, Submodule.Quotient.mk_eq_zero,
      coe_toLieSubmodule, mem_toSubmodule]
    rw [← h]; rw [H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_, LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
  · intro x hx
    let y := LieSubmodule.Quotient.mk' H.toLieSubmodule x
    have hy : y in LieModule.maxTrivSubmodule R H (L ⧸ H.toLieSubmodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie]; rw [LieSubmodule.Quotient.mk_eq_zero]; rw [coe_bracket_of_module]; rw [Submodule.coe_mk]; rw [mem_toLieSubmodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa [y] using h y hy

中文:
定理 normalizer_eq_self_iff
  证明: by
  rw [LieSubmodule.eq_bot_iff]
  refine ⟨fun h => ?_, fun h => le_antisymm ?_ H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x in H by rwa [Submodule.Quotient.quot_mk_eq_mk, Submodule.Quotient.mk_eq_zero,
      coe_toLieSubmodule, mem_toSubmodule]
    rw [← h]; rw [H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_, LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
  · intro x hx
    let y := LieSubmodule.Quotient.mk' H.toLieSubmodule x
    have hy : y in LieModule.maxTrivSubmodule R H (L ⧸ H.toLieSubmodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie]; rw [LieSubmodule.Quotient.mk_eq_zero]; rw [coe_bracket_of_module]; rw [Submodule.coe_mk]; rw [mem_toLieSubmodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa [y] using h y hy

Depends on / 依赖: H.le_normalizer, H.mem_normalizer_iff, H.toLieSubmodule, LieModuleHom, LieModuleHom.map_lie, LieSubmodule, LieSubmodule.Quotient.mk, LieSubmodule.Quotient.mk_eq_zero, LieSubmodule.eq_bot_iff, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.quot_mk_eq_mk, coe_toLieSubmodule, eq_bot_iff, le_antisymm, le_normalizer, map_lie, mem_normalizer_iff, mem_toSubmodule
-/
theorem normalizer_eq_self_iff :
    H.normalizer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  refine ⟨fun h => ?_, fun h => le_antisymm ?_ H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x in H by rwa [Submodule.Quotient.quot_mk_eq_mk, Submodule.Quotient.mk_eq_zero,
      coe_toLieSubmodule, mem_toSubmodule]
    rw [← h]; rw [H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_, LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
  · intro x hx
    let y := LieSubmodule.Quotient.mk' H.toLieSubmodule x
    have hy : y in LieModule.maxTrivSubmodule R H (L ⧸ H.toLieSubmodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie]; rw [LieSubmodule.Quotient.mk_eq_zero]; rw [coe_bracket_of_module]; rw [Submodule.coe_mk]; rw [mem_toLieSubmodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa [y] using h y hy

end LieSubalgebra
