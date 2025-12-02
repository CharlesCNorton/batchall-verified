(** * Clan Batchall: Formal Verification of Ritual Combat Protocol

    Machine-checked formalization of the Clan challenge system from BattleTech.
    This development formalizes the batchall ritual, force bidding mechanics,
    and honor accounting as a verified state machine with well-foundedness
    guarantees ensuring all bidding sequences terminate.

    The batchall (from "batch" meaning "to call") is the formal Clan ritual
    of challenge. A Clan warrior issues the batchall to claim a prize, the
    defender responds with their defending force, and both sides then bid
    DOWN their committed forces to demonstrate martial prowess and honor.

    Example exchange:

      "I am Star Colonel Timur Malthus, Clan Jade Falcon.
       We claim this enclave. With what do you defend?"

      "Star Captain Dwillt Radick, Clan Wolf. One Trinary."

      "Aff. I bid one Binary."

      "Bargained well and done."

    Author: Charles C. Norton
    Date: December 2025
*)

(** ** Table of Contents

    - Part I: Foundational Imports and Setup
    - Part II: Domain Types (Clans, Ranks, Units)
    - Part III: Force Metrics and Ordering
    - Part IV: Trials, Stakes, Honor Codes
    - Part V: Protocol Messages and Actions
    - Part VI: State Machine and Transitions
    - Part VII: Honor Accounting System
    - Part VIII: Internal Clan Bidding
    - Part IX: Termination and Soundness
    - Part X: Main Theorems and Examples
*)

From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Relations.
From Coq Require Import Wellfounded.
From Coq Require Import Lia.
From Coq Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Part I: Foundational Setup *)

(** We work primarily in nat_scope for force metrics calculations. *)
Open Scope nat_scope.

(** * Part II: Domain Types *)

(** ** Section 2.1: The Clans

    The Clans are the descendants of the Star League Defense Force who
    followed General Aleksandr Kerensky into exile. Each Clan developed
    unique warrior traditions and combat doctrines.

    - ClanWolf: Wardens who preserved Kerensky's vision of protecting the Inner Sphere
    - ClanJadeFalcon: Aggressive Crusaders, bitter rivals of the Wolves
    - ClanSmokeJaguar: Brutal warriors known for savagery, destroyed in 3060
    - ClanGhostBear: Patient, methodical warriors who value family bonds
    - ClanNovaCat: Mystical warriors guided by visions
    - ClanDiamondShark: Merchant warriors, formerly Sea Fox
    - ClanSteelViper: Traditionalists absorbed by other Clans
    - ClanHellsHorses: Combined-arms specialists favoring vehicles
    - ClanCoyote: Innovators and founders of the OmniMech
    - ClanStarAdder: Careful strategists and political manipulators
    - ClanBloodSpirit: Isolationists, destroyed in the Wars of Reaving
    - ClanFireMandrill: Fractious Clan organized into Kindraa
    - ClanCloudCobra: Religious warriors devoted to "The Way"
    - ClanSnowRaven: Naval specialists and merchant-warriors
    - ClanGoliathScorpion: Seekers of Star League artifacts
    - ClanIceHellion: Swift raiders known for aggressive tactics
*)

Inductive Clan : Type :=
  | ClanWolf
  | ClanJadeFalcon
  | ClanSmokeJaguar
  | ClanGhostBear
  | ClanNovaCat
  | ClanDiamondShark
  | ClanSteelViper
  | ClanHellsHorses
  | ClanCoyote
  | ClanStarAdder
  | ClanBloodSpirit
  | ClanFireMandrill
  | ClanCloudCobra
  | ClanSnowRaven
  | ClanGoliathScorpion
  | ClanIceHellion
  | ClanGeneric (id : nat).

(** Decidable equality for Clans. *)
Definition clan_eq_dec : forall (c1 c2 : Clan), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

(** Boolean equality with correctness proof. *)
Definition clan_eqb (c1 c2 : Clan) : bool :=
  if clan_eq_dec c1 c2 then true else false.

Lemma clan_eqb_eq : forall c1 c2, clan_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2. unfold clan_eqb.
  destruct (clan_eq_dec c1 c2); split; intros; auto; discriminate.
Qed.

Lemma clan_eqb_refl : forall c, clan_eqb c c = true.
Proof.
  intros c. apply clan_eqb_eq. reflexivity.
Qed.

(** ** Section 2.2: Warrior Ranks

    Clan military ranks follow a strict hierarchy. Warriors advance through
    Trials of Position. The touman (military) is organized from Points (5 units)
    up through Stars, Binaries, Trinaries, Clusters, and Galaxies.

    - Warrior: Basic fighter, no command authority
    - Point Commander: Commands a Point (5 units)
    - Star Commander: Commands a Star (5 Points = 25 units)
    - Star Captain: Commands a Binary/Trinary (2-3 Stars)
    - Star Colonel: Commands a Cluster (3-5 Binaries)
    - Galaxy Commander: Commands a Galaxy (3-5 Clusters)
    - Khan: Supreme military commander of a Clan
    - saKhan: Second-in-command, often leads combat operations
    - Loremaster: Keeper of traditions, arbiter of disputes
*)

Inductive Rank : Type :=
  | Warrior
  | PointCommander
  | StarCommander
  | StarCaptain
  | StarColonel
  | GalaxyCommander
  | Khan
  | SaKhan
  | Loremaster.

(** Numeric encoding for rank comparison. *)
Definition rank_to_nat (r : Rank) : nat :=
  match r with
  | Warrior => 0
  | PointCommander => 1
  | StarCommander => 2
  | StarCaptain => 3
  | StarColonel => 4
  | GalaxyCommander => 5
  | Khan => 6
  | SaKhan => 7
  | Loremaster => 8
  end.

Definition rank_le (r1 r2 : Rank) : bool :=
  rank_to_nat r1 <=? rank_to_nat r2.

Definition rank_lt (r1 r2 : Rank) : bool :=
  rank_to_nat r1 <? rank_to_nat r2.

Definition rank_eq_dec : forall (r1 r2 : Rank), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

(** ** Section 2.3: Commanders

    A Commander represents a warrior authorized to issue or respond to batchall.
    Bloodnamed warriors have won a Trial of Bloodright and carry the genetic
    legacy name of an original SLDF warrior who joined the Exodus. *)

Record Commander : Type := mkCommander {
  cmd_id : nat;
  cmd_clan : Clan;
  cmd_rank : Rank;
  cmd_bloodnamed : bool
}.

Definition commander_eq_dec : forall (c1 c2 : Commander), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
  - apply Bool.bool_dec.
  - apply rank_eq_dec.
  - apply clan_eq_dec.
  - apply Nat.eq_dec.
Defined.

(** A commander may issue batchall if they hold appropriate rank. *)
Definition may_issue_batchall (c : Commander) : bool :=
  rank_le StarCaptain (cmd_rank c).

(** ** Section 2.4: Unit Classifications

    Combat units in the Clans are classified by type and weight.

    Unit Classes:
    - OmniMech: Modular BattleMech with swappable weapon pods
    - BattleMech: Standard 'Mech without OmniMech modularity
    - ProtoMech: Small 2-9 ton combat units
    - Aerospace: Conventional aerospace fighters
    - OmniFighter: Modular aerospace fighters
    - Vehicle: Ground combat vehicles
    - BattleArmor: Powered infantry armor (non-Elemental)
    - Elemental: Clan-specific genetically enhanced infantry in battle armor
    - Infantry: Unarmored foot soldiers (dezgra - dishonorable)
*)

Inductive UnitClass : Type :=
  | OmniMech
  | BattleMech
  | ProtoMech
  | Aerospace
  | OmniFighter
  | Vehicle
  | BattleArmor
  | Elemental
  | Infantry.

(** Weight classes determine a unit's tonnage range. *)
Inductive WeightClass : Type :=
  | Ultralight
  | Light
  | Medium
  | Heavy
  | Assault
  | SuperHeavy.

Definition weight_to_nat (w : WeightClass) : nat :=
  match w with
  | Ultralight => 0
  | Light => 1
  | Medium => 2
  | Heavy => 3
  | Assault => 4
  | SuperHeavy => 5
  end.

(** ** Section 2.5: Combat Units

    A Unit represents a single combat asset that can be committed to battle. *)

Record Unit : Type := mkUnit {
  unit_id : nat;
  unit_class : UnitClass;
  unit_weight : WeightClass;
  unit_tonnage : nat;
  unit_skill : nat;
  unit_is_elite : bool;
  unit_is_clan : bool
}.

(** A Force is a list of units committed to combat. *)
Definition Force : Type := list Unit.

(** * Part III: Force Metrics and Ordering *)

(** ** Section 3.1: Force Metrics

    Force metrics provide a quantitative summary of a force's combat potential.
    These metrics are used for bid comparison in the batchall ritual.

    - fm_count: Number of units in the force
    - fm_tonnage: Total tonnage of all units
    - fm_elite_count: Number of elite-rated units
    - fm_clan_count: Number of Clan-tech units (vs Inner Sphere salvage)
*)

Record ForceMetrics : Type := mkForceMetrics {
  fm_count : nat;
  fm_tonnage : nat;
  fm_elite_count : nat;
  fm_clan_count : nat
}.

(** The empty force has zero metrics. *)
Definition empty_metrics : ForceMetrics :=
  mkForceMetrics 0 0 0 0.

(** Convert a single unit to its metric contribution. *)
Definition unit_to_metrics (u : Unit) : ForceMetrics :=
  mkForceMetrics
    1
    (unit_tonnage u)
    (if unit_is_elite u then 1 else 0)
    (if unit_is_clan u then 1 else 0).

(** Metrics form a commutative monoid under addition. *)
Definition metrics_add (m1 m2 : ForceMetrics) : ForceMetrics :=
  mkForceMetrics
    (fm_count m1 + fm_count m2)
    (fm_tonnage m1 + fm_tonnage m2)
    (fm_elite_count m1 + fm_elite_count m2)
    (fm_clan_count m1 + fm_clan_count m2).

(** Compute the metrics of a force by folding over units. *)
Definition force_metrics (f : Force) : ForceMetrics :=
  fold_right (fun u acc => metrics_add (unit_to_metrics u) acc) empty_metrics f.

(** ** Section 3.2: Metrics Monoid Laws *)

Lemma metrics_add_comm : forall m1 m2,
  metrics_add m1 m2 = metrics_add m2 m1.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2].
  unfold metrics_add. simpl.
  rewrite (Nat.add_comm c1 c2).
  rewrite (Nat.add_comm t1 t2).
  rewrite (Nat.add_comm e1 e2).
  rewrite (Nat.add_comm l1 l2).
  reflexivity.
Qed.

Lemma metrics_add_assoc : forall m1 m2 m3,
  metrics_add m1 (metrics_add m2 m3) = metrics_add (metrics_add m1 m2) m3.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2] [c3 t3 e3 l3].
  unfold metrics_add. simpl.
  rewrite (Nat.add_assoc c1 c2 c3).
  rewrite (Nat.add_assoc t1 t2 t3).
  rewrite (Nat.add_assoc e1 e2 e3).
  rewrite (Nat.add_assoc l1 l2 l3).
  reflexivity.
Qed.

Lemma metrics_add_empty_l : forall m,
  metrics_add empty_metrics m = m.
Proof.
  intros [c t e l]. unfold metrics_add, empty_metrics. reflexivity.
Qed.

Lemma metrics_add_empty_r : forall m,
  metrics_add m empty_metrics = m.
Proof.
  intros [c t e l]. unfold metrics_add, empty_metrics. simpl.
  rewrite Nat.add_0_r. rewrite Nat.add_0_r.
  rewrite Nat.add_0_r. rewrite Nat.add_0_r.
  reflexivity.
Qed.

(** ** Section 3.3: Force Metrics Computation *)

Lemma force_metrics_nil : force_metrics [] = empty_metrics.
Proof. reflexivity. Qed.

Lemma force_metrics_cons : forall u f,
  force_metrics (u :: f) = metrics_add (unit_to_metrics u) (force_metrics f).
Proof. reflexivity. Qed.

Lemma force_metrics_app : forall f1 f2,
  force_metrics (f1 ++ f2) = metrics_add (force_metrics f1) (force_metrics f2).
Proof.
  induction f1 as [|u rest IH]; intros f2.
  - simpl. rewrite metrics_add_empty_l. reflexivity.
  - simpl. rewrite IH. rewrite metrics_add_assoc. reflexivity.
Qed.

(** ** Section 3.4: Partial Order on Force Metrics

    Force metrics form a partial order under componentwise comparison.
    This order is used to determine valid bids: a new bid must be
    strictly less than the previous bid in this order. *)

Definition fm_le (m1 m2 : ForceMetrics) : Prop :=
  fm_count m1 <= fm_count m2 /\
  fm_tonnage m1 <= fm_tonnage m2 /\
  fm_elite_count m1 <= fm_elite_count m2 /\
  fm_clan_count m1 <= fm_clan_count m2.

Definition fm_lt (m1 m2 : ForceMetrics) : Prop :=
  fm_le m1 m2 /\ m1 <> m2.

(** Decidability of the ordering. *)
Definition fm_le_dec (m1 m2 : ForceMetrics) : {fm_le m1 m2} + {~ fm_le m1 m2}.
Proof.
  unfold fm_le.
  destruct (le_dec (fm_count m1) (fm_count m2));
  destruct (le_dec (fm_tonnage m1) (fm_tonnage m2));
  destruct (le_dec (fm_elite_count m1) (fm_elite_count m2));
  destruct (le_dec (fm_clan_count m1) (fm_clan_count m2));
  try (left; auto; fail);
  right; intros [H1 [H2 [H3 H4]]]; contradiction.
Defined.

Definition fm_eq_dec : forall m1 m2 : ForceMetrics, {m1 = m2} + {m1 <> m2}.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2].
  destruct (Nat.eq_dec c1 c2);
  destruct (Nat.eq_dec t1 t2);
  destruct (Nat.eq_dec e1 e2);
  destruct (Nat.eq_dec l1 l2);
  try (left; congruence);
  right; congruence.
Defined.

Definition fm_lt_dec (m1 m2 : ForceMetrics) : {fm_lt m1 m2} + {~ fm_lt m1 m2}.
Proof.
  unfold fm_lt.
  destruct (fm_le_dec m1 m2).
  - destruct (fm_eq_dec m1 m2).
    + right. intros [_ Hneq]. contradiction.
    + left. auto.
  - right. intros [Hle _]. contradiction.
Defined.

(** ** Section 3.5: Partial Order Laws *)

Lemma fm_le_refl : forall m, fm_le m m.
Proof.
  intros m. unfold fm_le. auto.
Qed.

Lemma fm_le_trans : forall m1 m2 m3,
  fm_le m1 m2 -> fm_le m2 m3 -> fm_le m1 m3.
Proof.
  intros m1 m2 m3 [H1a [H1b [H1c H1d]]] [H2a [H2b [H2c H2d]]].
  unfold fm_le. repeat split; lia.
Qed.

Lemma fm_le_antisym : forall m1 m2,
  fm_le m1 m2 -> fm_le m2 m1 -> m1 = m2.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2].
  unfold fm_le. simpl.
  intros [H1a [H1b [H1c H1d]]] [H2a [H2b [H2c H2d]]].
  f_equal; lia.
Qed.

(** ** Section 3.6: Well-Founded Order

    The key property for termination: the strict order on metrics is
    well-founded. This ensures bidding cannot continue forever. *)

Definition fm_measure (m : ForceMetrics) : nat :=
  fm_count m + fm_tonnage m + fm_elite_count m + fm_clan_count m.

Lemma fm_lt_implies_measure_lt : forall m1 m2,
  fm_lt m1 m2 -> fm_measure m1 < fm_measure m2.
Proof.
  intros m1 m2 [[H1 [H2 [H3 H4]]] Hneq].
  unfold fm_measure.
  destruct m1 as [c1 t1 e1 l1].
  destruct m2 as [c2 t2 e2 l2].
  simpl in *.
  destruct (Nat.eq_dec (c1 + t1 + e1 + l1) (c2 + t2 + e2 + l2)).
  - exfalso. apply Hneq.
    assert (c1 = c2) by lia.
    assert (t1 = t2) by lia.
    assert (e1 = e2) by lia.
    assert (l1 = l2) by lia.
    subst. reflexivity.
  - lia.
Qed.

Theorem fm_lt_well_founded : well_founded fm_lt.
Proof.
  apply well_founded_lt_compat with (f := fm_measure).
  intros m1 m2 Hlt. apply fm_lt_implies_measure_lt. exact Hlt.
Qed.

(** ** Section 3.7: Force Ordering *)

Definition force_le (f1 f2 : Force) : Prop :=
  fm_le (force_metrics f1) (force_metrics f2).

Definition force_lt (f1 f2 : Force) : Prop :=
  fm_lt (force_metrics f1) (force_metrics f2).

Lemma force_metrics_monotone : forall u f,
  fm_le (force_metrics f) (force_metrics (u :: f)).
Proof.
  intros u f. unfold fm_le. simpl.
  unfold metrics_add, unit_to_metrics. simpl.
  repeat split; lia.
Qed.

Lemma force_metrics_nonneg : forall f,
  fm_count (force_metrics f) >= 0 /\
  fm_tonnage (force_metrics f) >= 0 /\
  fm_elite_count (force_metrics f) >= 0 /\
  fm_clan_count (force_metrics f) >= 0.
Proof.
  induction f as [|u rest IH].
  - simpl. repeat split; lia.
  - simpl. unfold metrics_add, unit_to_metrics. simpl.
    destruct IH as [H1 [H2 [H3 H4]]].
    repeat split; lia.
Qed.

(** * Part IV: Trials, Stakes, and Honor Codes *)

(** ** Section 4.1: Trial Types

    Clan society revolves around ritualized combat trials. Each trial type
    serves a specific purpose and carries different stakes and honor implications.

    - TrialOfPosition: Advancement in rank; warriors challenge superiors
    - TrialOfPossession: Claim resources, territory, bondsmen, or equipment
    - TrialOfRefusal: Protest a political or military decision
    - TrialOfGrievance: Personal dispute resolution between warriors
    - TrialOfBloodright: Competition for a Bloodname legacy
    - TrialOfAbjuration: Exile a warrior or unit from the Clan
    - TrialOfAnnihilation: Total destruction of target (extremely rare)
*)

Inductive TrialType : Type :=
  | TrialOfPosition
  | TrialOfPossession
  | TrialOfRefusal
  | TrialOfGrievance
  | TrialOfBloodright
  | TrialOfAbjuration
  | TrialOfAnnihilation.

Definition trial_eq_dec : forall t1 t2 : TrialType, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

(** Severity determines the stakes and scrutiny applied to the trial. *)
Definition trial_severity (t : TrialType) : nat :=
  match t with
  | TrialOfPosition => 1
  | TrialOfPossession => 2
  | TrialOfRefusal => 2
  | TrialOfGrievance => 1
  | TrialOfBloodright => 3
  | TrialOfAbjuration => 4
  | TrialOfAnnihilation => 5
  end.

(** Some trials require a Circle of Equals - observed by peer warriors. *)
Definition trial_requires_circle (t : TrialType) : bool :=
  match t with
  | TrialOfBloodright => true
  | TrialOfAnnihilation => true
  | _ => false
  end.

(** Annihilation trials are explicitly lethal - no hegira permitted. *)
Definition trial_is_lethal (t : TrialType) : bool :=
  match t with
  | TrialOfAnnihilation => true
  | _ => false
  end.

Lemma trial_severity_positive : forall t, trial_severity t >= 1.
Proof. intros t. destruct t; simpl; lia. Qed.

Lemma annihilation_most_severe : forall t,
  trial_severity t <= trial_severity TrialOfAnnihilation.
Proof. intros t. destruct t; simpl; lia. Qed.

(** ** Section 4.2: Prizes and Stakes

    The prize is what the challenger seeks to claim through the batchall. *)

Inductive Prize : Type :=
  | PrizeWorld (world_id : nat)
  | PrizeEnclave (enclave_id : nat)
  | PrizeFacility (facility_id : nat)
  | PrizeBloodright (bloodname_id : nat)
  | PrizeHonor
  | PrizeTrial (trial : TrialType).

Inductive Location : Type :=
  | LocPlanetSurface (world_id : nat) (region_id : nat)
  | LocOrbital (world_id : nat)
  | LocDeepSpace (sector_id : nat)
  | LocEnclave (enclave_id : nat).

Record Stakes : Type := mkStakes {
  stakes_attacker_prize : Prize;
  stakes_defender_prize : option Prize;
  stakes_hegira_allowed : bool
}.

(** ** Section 4.3: Zellbrigen - The Dueling Honor Code

    Zellbrigen is the Clan code of honorable one-on-one combat. Warriors
    declare targets, engage individually, and respect fallen opponents.
    Violation of Zellbrigen brings severe dishonor.

    Key rules:
    - One-on-one engagement (no "gang up" tactics)
    - No physical attacks (punching/kicking 'Mechs is dezgra)
    - Declare targets before engaging
    - Respect ejected pilots (no attacking ejection pods)
*)

Inductive ZellbrigenStatus : Type :=
  | ZellActive
  | ZellBroken (violator_id : nat)
  | ZellSuspended
  | ZellNotApplicable.

Record ZellbrigenRules : Type := mkZellbrigenRules {
  zell_one_on_one : bool;
  zell_no_physical : bool;
  zell_declare_targets : bool;
  zell_respect_ejections : bool
}.

Definition strict_zellbrigen : ZellbrigenRules :=
  mkZellbrigenRules true true true true.

Definition relaxed_zellbrigen : ZellbrigenRules :=
  mkZellbrigenRules true false false true.

Inductive ZellbrigenViolation : Type :=
  | ViolGangUp
  | ViolPhysicalAttack
  | ViolUndeclaredTarget
  | ViolAttackEjected
  | ViolOther (code : nat).

Definition zell_violation_severity (v : ZellbrigenViolation) : nat :=
  match v with
  | ViolGangUp => 3
  | ViolPhysicalAttack => 1
  | ViolUndeclaredTarget => 2
  | ViolAttackEjected => 5
  | ViolOther _ => 1
  end.

Lemma zell_violation_positive : forall v, zell_violation_severity v >= 1.
Proof. intros v. destruct v; simpl; lia. Qed.

(** ** Section 4.4: Safcon - Safe Conduct Protocol

    Safcon (safe conduct) protects DropShips and JumpShips traveling to
    and from a battle. Attacking vessels under safcon is severely dishonorable.
*)

Inductive SafconStatus : Type :=
  | SafconGranted
  | SafconDenied
  | SafconViolated (by_side : nat)
  | SafconExpired
  | SafconNotRequested.

Record SafconTerms : Type := mkSafconTerms {
  safcon_granted : bool;
  safcon_jumpship_protected : bool;
  safcon_dropship_protected : bool;
  safcon_duration_hours : nat;
  safcon_granting_clan : Clan
}.

Definition default_safcon (grantor : Clan) : SafconTerms :=
  mkSafconTerms true true true 72 grantor.

Definition safcon_active (s : SafconTerms) : bool :=
  safcon_granted s && negb (Nat.eqb (safcon_duration_hours s) 0).

Lemma safcon_default_active : forall c, safcon_active (default_safcon c) = true.
Proof. intros c. reflexivity. Qed.

Inductive SafconViolationType : Type :=
  | SafconAttackJumpship
  | SafconAttackDropship
  | SafconAttackInTransit
  | SafconDenyLanding.

Definition safcon_violation_dishonor (v : SafconViolationType) : nat :=
  match v with
  | SafconAttackJumpship => 10
  | SafconAttackDropship => 5
  | SafconAttackInTransit => 8
  | SafconDenyLanding => 3
  end.

Lemma safcon_violation_dishonorable : forall v,
  safcon_violation_dishonor v >= 3.
Proof. intros v. destruct v; simpl; lia. Qed.

(** ** Section 4.5: Hegira - Honorable Retreat

    Hegira is the right to withdraw from battle with honor intact.
    A defender may request hegira if they acknowledge defeat.
    The attacker may grant or deny; denial is dishonorable.
    Violating granted hegira (attacking retreating forces) is severely dishonorable.
*)

Inductive HegiraAction : Type :=
  | HegiraRequest
  | HegiraGrant
  | HegiraDeny
  | HegiraAccept
  | HegiraViolate.

(** * Part V: Protocol Messages and Actions *)

(** ** Section 5.1: Sides

    Every batchall has two sides: the challenger (attacker) who issues
    the batchall, and the defender who must respond. *)

Inductive Side : Type := Attacker | Defender.

Definition side_eq_dec : forall s1 s2 : Side, {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.

Definition side_eqb (s1 s2 : Side) : bool :=
  match s1, s2 with
  | Attacker, Attacker => true
  | Defender, Defender => true
  | _, _ => false
  end.

(** ** Section 5.2: Force Bids

    A ForceBid represents a commitment of forces to the battle.
    During bidding, warriors reduce their bids to demonstrate confidence. *)

Record ForceBid : Type := mkForceBid {
  bid_side : Side;
  bid_force : Force;
  bid_commander : Commander
}.

Definition bid_metrics (b : ForceBid) : ForceMetrics :=
  force_metrics (bid_force b).

Definition bid_lt (b1 b2 : ForceBid) : Prop :=
  bid_side b1 = bid_side b2 /\ fm_lt (bid_metrics b1) (bid_metrics b2).

(** ** Section 5.3: Protocol Messages

    The batchall ritual involves structured message exchange. *)

Record BatchallChallenge : Type := mkBatchallChallenge {
  chal_challenger : Commander;
  chal_prize : Prize;
  chal_initial_force : Force
}.

Record BatchallResponse : Type := mkBatchallResponse {
  resp_defender : Commander;
  resp_location : Location;
  resp_force : Force;
  resp_counter_stakes : option Stakes
}.

(** ** Section 5.4: Refusal Reasons

    A defender may refuse a challenge for specific reasons. Some reasons
    are honorable, others carry dishonor. *)

Inductive RefusalReason : Type :=
  | RefusalDishonorableConduct
  | RefusalNoJurisdiction
  | RefusalInvalidChallenger
  | RefusalAlreadyContested
  | RefusalOther (code : nat).

(** ** Section 5.5: Protocol Actions

    All possible actions in the batchall protocol. *)

Inductive ProtocolAction : Type :=
  | ActChallenge (challenge : BatchallChallenge)
  | ActRespond (response : BatchallResponse)
  | ActRefuse (reason : RefusalReason)
  | ActBid (bid : ForceBid)
  | ActPass (side : Side)
  | ActClose
  | ActBreakBid
  | ActWithdraw (side : Side).

(** * Part VI: State Machine and Transitions *)

(** ** Section 6.1: Ready Status

    During bidding, each side may signal readiness to accept current bids.
    When both sides pass consecutively, bidding concludes. *)

Inductive ReadyStatus : Type :=
  | NeitherReady
  | AttackerReady
  | DefenderReady
  | BothReady.

(** ** Section 6.2: Protocol Phases

    The batchall protocol progresses through well-defined phases. *)

Inductive BatchallPhase : Type :=
  | PhaseIdle
  | PhaseChallenged (challenge : BatchallChallenge)
  | PhaseResponded (challenge : BatchallChallenge) (response : BatchallResponse)
  | PhaseBidding (challenge : BatchallChallenge)
                 (response : BatchallResponse)
                 (attacker_bid : ForceBid)
                 (defender_bid : ForceBid)
                 (bid_history : list ForceBid)
                 (ready : ReadyStatus)
  | PhaseRefused (challenge : BatchallChallenge) (reason : RefusalReason)
  | PhaseAgreed (challenge : BatchallChallenge)
                (response : BatchallResponse)
                (final_attacker_bid : ForceBid)
                (final_defender_bid : ForceBid)
  | PhaseAborted.

(** ** Section 6.3: Transition Rules

    The core state machine defining valid protocol transitions.
    Each constructor represents one valid state transition. *)

Inductive BatchallStep : BatchallPhase -> ProtocolAction -> BatchallPhase -> Prop :=

  | StepChallenge : forall chal,
      BatchallStep PhaseIdle
                   (ActChallenge chal)
                   (PhaseChallenged chal)

  | StepRefuse : forall chal reason,
      BatchallStep (PhaseChallenged chal)
                   (ActRefuse reason)
                   (PhaseRefused chal reason)

  | StepRespond : forall chal resp,
      BatchallStep (PhaseChallenged chal)
                   (ActRespond resp)
                   (PhaseResponded chal resp)

  | StepStartBidding : forall chal resp,
      let atk_bid := mkForceBid Attacker (chal_initial_force chal) (chal_challenger chal) in
      let def_bid := mkForceBid Defender (resp_force resp) (resp_defender resp) in
      BatchallStep (PhaseResponded chal resp)
                   (ActBid atk_bid)
                   (PhaseBidding chal resp atk_bid def_bid [] NeitherReady)

  | StepAttackerBid : forall chal resp atk_bid def_bid hist ready new_bid,
      bid_side new_bid = Attacker ->
      fm_lt (bid_metrics new_bid) (bid_metrics atk_bid) ->
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist ready)
                   (ActBid new_bid)
                   (PhaseBidding chal resp new_bid def_bid (atk_bid :: hist) NeitherReady)

  | StepDefenderBid : forall chal resp atk_bid def_bid hist ready new_bid,
      bid_side new_bid = Defender ->
      fm_lt (bid_metrics new_bid) (bid_metrics def_bid) ->
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist ready)
                   (ActBid new_bid)
                   (PhaseBidding chal resp atk_bid new_bid (def_bid :: hist) NeitherReady)

  | StepAttackerPass : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist NeitherReady)
                   (ActPass Attacker)
                   (PhaseBidding chal resp atk_bid def_bid hist AttackerReady)

  | StepDefenderPass : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist NeitherReady)
                   (ActPass Defender)
                   (PhaseBidding chal resp atk_bid def_bid hist DefenderReady)

  | StepCloseFromAttackerReady : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist AttackerReady)
                   (ActPass Defender)
                   (PhaseAgreed chal resp atk_bid def_bid)

  | StepCloseFromDefenderReady : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist DefenderReady)
                   (ActPass Attacker)
                   (PhaseAgreed chal resp atk_bid def_bid)

  | StepWithdraw : forall chal resp atk_bid def_bid hist ready side,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist ready)
                   (ActWithdraw side)
                   PhaseAborted.

(** ** Section 6.4: Protocol Traces

    A trace is a sequence of valid transitions from a starting phase. *)

Inductive BatchallTrace : BatchallPhase -> Type :=
  | TraceNil : forall phase, BatchallTrace phase
  | TraceCons : forall phase1 action phase2,
      BatchallStep phase1 action phase2 ->
      BatchallTrace phase2 ->
      BatchallTrace phase1.

Fixpoint trace_length {phase : BatchallPhase} (t : BatchallTrace phase) : nat :=
  match t with
  | TraceNil _ => 0
  | @TraceCons _ _ _ _ rest => S (trace_length rest)
  end.

(** ** Section 6.5: Phase Predicates *)

Definition is_terminal (phase : BatchallPhase) : Prop :=
  match phase with
  | PhaseAgreed _ _ _ _ => True
  | PhaseRefused _ _ => True
  | PhaseAborted => True
  | _ => False
  end.

Definition is_bidding (phase : BatchallPhase) : Prop :=
  match phase with
  | PhaseBidding _ _ _ _ _ _ => True
  | _ => False
  end.

Definition is_terminal_dec (phase : BatchallPhase) : {is_terminal phase} + {~ is_terminal phase}.
Proof.
  destruct phase; simpl; auto; right; auto.
Defined.

(** * Part VII: Honor Accounting System *)

(** ** Section 7.1: Honor Type and Ledger

    Honor is tracked as signed integers - warriors can gain or lose honor.
    The ledger maps commanders to their current honor standing. *)

Open Scope Z_scope.

Definition Honor : Type := Z.

Record HonorLedger : Type := mkHonorLedger {
  ledger_honor : Commander -> Honor
}.

(** ** Section 7.2: Unified Honor Events

    All honor-affecting events are unified into a single type.
    This ensures consistent honor accounting across all game systems. *)

Inductive HonorEvent : Type :=
  | HEvProtocol (action : ProtocolAction)
  | HEvZellbrigen (violation : ZellbrigenViolation)
  | HEvSafcon (violation : SafconViolationType)
  | HEvHegira (action : HegiraAction).

(** ** Section 7.3: Refusal Honor Deltas

    Different refusal reasons carry different honor implications. *)

Definition refusal_honor_delta (reason : RefusalReason) : Honor :=
  match reason with
  | RefusalDishonorableConduct => 2
  | RefusalNoJurisdiction => 0
  | RefusalInvalidChallenger => 1
  | RefusalAlreadyContested => 0
  | RefusalOther _ => -1
  end.

(** ** Section 7.4: Hegira Honor Deltas *)

Definition hegira_honor_delta (h : HegiraAction) : Honor :=
  match h with
  | HegiraRequest => 0
  | HegiraGrant => 3
  | HegiraDeny => -2
  | HegiraAccept => 1
  | HegiraViolate => -15
  end.

(** ** Section 7.5: Protocol Action Honor Deltas *)

Definition protocol_honor_delta (action : ProtocolAction) : Honor :=
  match action with
  | ActChallenge _ => 1
  | ActRespond _ => 1
  | ActRefuse reason => refusal_honor_delta reason
  | ActBid _ => 0
  | ActPass _ => 0
  | ActClose => 1
  | ActBreakBid => -10
  | ActWithdraw _ => -2
  end.

(** ** Section 7.6: Unified Honor Delta *)

Definition honor_event_delta (event : HonorEvent) : Honor :=
  match event with
  | HEvProtocol action => protocol_honor_delta action
  | HEvZellbrigen v => Z.opp (Z.of_nat (zell_violation_severity v))
  | HEvSafcon v => Z.opp (Z.of_nat (safcon_violation_dishonor v))
  | HEvHegira h => hegira_honor_delta h
  end.

(** ** Section 7.7: Ledger Updates *)

Definition update_honor (ledger : HonorLedger) (actor : Commander) (delta : Honor)
    : HonorLedger :=
  mkHonorLedger (fun c =>
    if Nat.eqb (cmd_id c) (cmd_id actor)
    then ledger_honor ledger c + delta
    else ledger_honor ledger c).

Definition apply_event_honor (ledger : HonorLedger) (event : HonorEvent)
    (actor : Commander) : HonorLedger :=
  update_honor ledger actor (honor_event_delta event).

(** ** Section 7.8: Honor Lemmas *)

Lemma honor_update_self : forall ledger actor delta,
  ledger_honor (update_honor ledger actor delta) actor =
  (ledger_honor ledger actor + delta)%Z.
Proof.
  intros ledger actor delta.
  unfold update_honor. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma honor_update_other : forall ledger actor other delta,
  cmd_id actor <> cmd_id other ->
  ledger_honor (update_honor ledger actor delta) other =
  ledger_honor ledger other.
Proof.
  intros ledger actor other delta Hneq.
  unfold update_honor. simpl.
  destruct (Nat.eqb (cmd_id other) (cmd_id actor)) eqn:Heq.
  - apply Nat.eqb_eq in Heq. symmetry in Heq. contradiction.
  - reflexivity.
Qed.

Lemma hegira_grant_honorable : (hegira_honor_delta HegiraGrant > 0)%Z.
Proof. simpl. lia. Qed.

Lemma hegira_violate_severely_dishonorable :
  (hegira_honor_delta HegiraViolate <= -10)%Z.
Proof. simpl. lia. Qed.

Close Scope Z_scope.

(** * Part VIII: Internal Clan Bidding *)

(** ** Section 8.1: Internal Bidding Concepts

    When a Clan wins the right to a batchall, internal bidding determines
    which warrior actually leads the force. Warriors compete by bidding
    down their requested forces - the lowest bid wins the honor of combat. *)

Record SubCommander : Type := mkSubCommander {
  subcmd_id : nat;
  subcmd_commander : Commander
}.

Record InternalCandidate : Type := mkInternalCandidate {
  icand_subcommander : SubCommander;
  icand_force : Force
}.

Definition icand_metrics (c : InternalCandidate) : ForceMetrics :=
  force_metrics (icand_force c).

Definition icand_lt (c1 c2 : InternalCandidate) : Prop :=
  fm_lt (icand_metrics c1) (icand_metrics c2).

(** ** Section 8.2: Sequential Internal Bidding *)

Inductive InternalPhase : Type :=
  | IPhaseIdle (candidates : list InternalCandidate)
  | IPhaseBidding (candidates : list InternalCandidate)
                  (current_winner : InternalCandidate)
                  (bid_history : list InternalCandidate)
  | IPhaseComplete (winner : InternalCandidate).

Inductive InternalAction : Type :=
  | IActStart (initial : InternalCandidate)
  | IActUndercut (new_candidate : InternalCandidate)
  | IActConcede.

Inductive InternalStep : InternalPhase -> InternalAction -> InternalPhase -> Prop :=
  | IStepStart : forall cands initial,
      In initial cands ->
      InternalStep (IPhaseIdle cands)
                   (IActStart initial)
                   (IPhaseBidding cands initial [])

  | IStepUndercut : forall cands current hist new_cand,
      icand_lt new_cand current ->
      InternalStep (IPhaseBidding cands current hist)
                   (IActUndercut new_cand)
                   (IPhaseBidding cands new_cand (current :: hist))

  | IStepConcede : forall cands current hist,
      InternalStep (IPhaseBidding cands current hist)
                   IActConcede
                   (IPhaseComplete current).

(** ** Section 8.3: Concurrent Internal Bidding

    For larger operations, multiple warriors may submit bids simultaneously.
    The best bid (lowest metrics, then by priority) wins. *)

Record ConcurrentBid : Type := mkConcurrentBid {
  cbid_candidate : InternalCandidate;
  cbid_timestamp : nat;
  cbid_priority : nat
}.

Definition cbid_metrics (cb : ConcurrentBid) : ForceMetrics :=
  icand_metrics (cbid_candidate cb).

Inductive ConcurrentPhase : Type :=
  | CPhaseCollecting (deadline : nat) (bids : list ConcurrentBid)
  | CPhaseResolving (bids : list ConcurrentBid)
  | CPhaseResolved (winner : ConcurrentBid).

Definition find_best_bid (bids : list ConcurrentBid) : option ConcurrentBid :=
  match bids with
  | [] => None
  | b :: rest =>
      Some (fold_left (fun acc cb =>
        if fm_le_dec (cbid_metrics cb) (cbid_metrics acc)
        then (if fm_le_dec (cbid_metrics acc) (cbid_metrics cb)
              then (if cbid_priority cb <? cbid_priority acc then cb else acc)
              else cb)
        else acc) rest b)
  end.

Inductive ConcurrentAction : Type :=
  | CActSubmit (bid : ConcurrentBid)
  | CActDeadline
  | CActResolve.

Inductive ConcurrentStep : ConcurrentPhase -> ConcurrentAction -> ConcurrentPhase -> Prop :=
  | CStepSubmit : forall deadline bids new_bid,
      ConcurrentStep (CPhaseCollecting deadline bids)
                     (CActSubmit new_bid)
                     (CPhaseCollecting deadline (new_bid :: bids))

  | CStepDeadline : forall deadline bids,
      bids <> [] ->
      ConcurrentStep (CPhaseCollecting deadline bids)
                     CActDeadline
                     (CPhaseResolving bids)

  | CStepResolve : forall bids winner,
      find_best_bid bids = Some winner ->
      ConcurrentStep (CPhaseResolving bids)
                     CActResolve
                     (CPhaseResolved winner).

(** * Part IX: Termination and Soundness Proofs *)

(** ** Section 9.1: Terminal States are Final *)

Lemma terminal_no_step : forall phase action phase',
  is_terminal phase ->
  ~ BatchallStep phase action phase'.
Proof.
  intros phase action phase' Hterm Hstep.
  destruct phase; simpl in Hterm; try contradiction.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
Qed.

(** ** Section 9.2: Protocol Determinism

    Given the same starting phase and action, there is exactly one
    resulting phase. The protocol is deterministic. *)

Theorem protocol_determinism : forall phase action phase1 phase2,
  BatchallStep phase action phase1 ->
  BatchallStep phase action phase2 ->
  phase1 = phase2.
Proof.
  intros phase action phase1 phase2 H1 H2.
  inversion H1; subst; inversion H2; subst; try reflexivity; try discriminate.
  all: try congruence.
Qed.

(** ** Section 9.3: Bidding Measure

    The bidding measure strictly decreases with each bid, ensuring termination. *)

Definition bid_measure (b : ForceBid) : nat := fm_measure (bid_metrics b).

Definition bidding_state_measure (atk_bid def_bid : ForceBid) (ready : ReadyStatus) : nat :=
  let base := 3 * (bid_measure atk_bid + bid_measure def_bid) in
  match ready with
  | NeitherReady => base + 2
  | AttackerReady => base + 1
  | DefenderReady => base + 1
  | BothReady => base
  end.

(** ** Section 9.4: Bidding Steps Decrease Measure *)

Lemma bid_decrease_implies_measure_decrease : forall atk atk' def ready,
  fm_measure (bid_metrics atk') < fm_measure (bid_metrics atk) ->
  bidding_state_measure atk' def NeitherReady < bidding_state_measure atk def ready.
Proof.
  intros atk atk' def ready Hlt.
  unfold bidding_state_measure, bid_measure. destruct ready; lia.
Qed.

Lemma def_bid_decrease_implies_measure_decrease : forall atk def def' ready,
  fm_measure (bid_metrics def') < fm_measure (bid_metrics def) ->
  bidding_state_measure atk def' NeitherReady < bidding_state_measure atk def ready.
Proof.
  intros atk def def' ready Hlt.
  unfold bidding_state_measure, bid_measure. destruct ready; lia.
Qed.

(** ** Section 9.5: Bidding Step Progress *)

Lemma bidding_step_decreases_or_terminal : forall chal resp atk def hist ready action phase',
  BatchallStep (PhaseBidding chal resp atk def hist ready) action phase' ->
  (exists atk' def' hist' ready',
     phase' = PhaseBidding chal resp atk' def' hist' ready' /\
     bidding_state_measure atk' def' ready' < bidding_state_measure atk def ready) \/
  is_terminal phase'.
Proof.
  intros chal resp atk def hist ready action phase' Hstep.
  inversion Hstep; subst.
  - left. do 4 eexists. split; [reflexivity|].
    apply bid_decrease_implies_measure_decrease.
    apply fm_lt_implies_measure_lt. assumption.
  - left. do 4 eexists. split; [reflexivity|].
    apply def_bid_decrease_implies_measure_decrease.
    apply fm_lt_implies_measure_lt. assumption.
  - left. do 4 eexists. split; [reflexivity|].
    unfold bidding_state_measure. lia.
  - left. do 4 eexists. split; [reflexivity|].
    unfold bidding_state_measure. lia.
  - right. simpl. trivial.
  - right. simpl. trivial.
  - right. simpl. trivial.
Qed.

(** ** Section 9.6: Bidding Termination *)

Theorem bidding_terminates_by_measure : forall (chal : BatchallChallenge) (resp : BatchallResponse)
    (atk def : ForceBid) (hist : list ForceBid) (ready : ReadyStatus),
  Acc (fun m1 m2 => m1 < m2) (bidding_state_measure atk def ready).
Proof.
  intros. apply Wf_nat.lt_wf.
Qed.

(** ** Section 9.7: No Infinite Bidding Sequences *)

Theorem no_infinite_bidding_sequence : forall (seq : nat -> ForceBid),
  (forall n, fm_lt (bid_metrics (seq (S n))) (bid_metrics (seq n))) ->
  False.
Proof.
  intros seq Hdesc.
  assert (Hmeas: forall n, fm_measure (bid_metrics (seq (S n))) < fm_measure (bid_metrics (seq n))).
  { intros n. apply fm_lt_implies_measure_lt. apply Hdesc. }
  assert (Hinc: forall n, fm_measure (bid_metrics (seq n)) + n <= fm_measure (bid_metrics (seq 0))).
  { induction n.
    - simpl. lia.
    - specialize (Hmeas n). lia. }
  specialize (Hinc (S (fm_measure (bid_metrics (seq 0))))).
  lia.
Qed.

(** ** Section 9.8: Well-Founded Bid Ordering *)

Theorem batchall_bid_well_founded :
  well_founded (fun b1 b2 => fm_lt (bid_metrics b1) (bid_metrics b2)).
Proof.
  apply well_founded_lt_compat with (f := bid_measure).
  intros b1 b2 [Hle Hneq].
  unfold bid_measure, fm_measure.
  destruct Hle as [H1 [H2 [H3 H4]]].
  destruct (bid_metrics b1) as [c1 t1 e1 l1].
  destruct (bid_metrics b2) as [c2 t2 e2 l2].
  simpl in *.
  destruct (Nat.eq_dec (c1 + t1 + e1 + l1) (c2 + t2 + e2 + l2)).
  - exfalso. apply Hneq.
    assert (c1 = c2) by lia.
    assert (t1 = t2) by lia.
    assert (e1 = e2) by lia.
    assert (l1 = l2) by lia.
    subst. reflexivity.
  - lia.
Qed.

(** * Part X: Main Theorems and Examples *)

(** ** Section 10.1: Battle Outcomes *)

Record ExternalResult : Type := mkExternalResult {
  ext_challenge : BatchallChallenge;
  ext_response : BatchallResponse;
  ext_attacker_bid : ForceBid;
  ext_defender_bid : ForceBid
}.

Record InternalResult : Type := mkInternalResult {
  int_winner : InternalCandidate
}.

Inductive BattleOutcome : Type :=
  | OutcomeAgreed (external : ExternalResult)
                  (attacker_internal : option InternalResult)
                  (defender_internal : option InternalResult)
  | OutcomeRefused (challenge : BatchallChallenge) (reason : RefusalReason)
  | OutcomeAborted.

(** ** Section 10.2: Outcome Predicates *)

Definition BargainedWellAndDone (outcome : BattleOutcome) : Prop :=
  match outcome with
  | OutcomeAgreed _ _ _ => True
  | _ => False
  end.

Definition HonorableConclusion (outcome : BattleOutcome) : Prop :=
  match outcome with
  | OutcomeAgreed _ _ _ => True
  | OutcomeRefused _ RefusalDishonorableConduct => True
  | _ => False
  end.

(** ** Section 10.3: Example - Honorable Batchall Is Possible *)

Theorem honorable_batchall_possible :
  exists chal resp,
    BatchallStep PhaseIdle (ActChallenge chal) (PhaseChallenged chal) /\
    BatchallStep (PhaseChallenged chal) (ActRespond resp) (PhaseResponded chal resp).
Proof.
  exists (mkBatchallChallenge
            (mkCommander 0 ClanWolf StarColonel true)
            (PrizeEnclave 1)
            []).
  exists (mkBatchallResponse
            (mkCommander 1 ClanJadeFalcon StarCaptain true)
            (LocEnclave 1)
            []
            None).
  split.
  - constructor.
  - constructor.
Qed.

(** ** Section 10.4: Sublist Relation for Force Composition *)

Inductive Sublist {A : Type} : list A -> list A -> Prop :=
  | SublistNil : forall l, Sublist [] l
  | SublistSkip : forall x l1 l2, Sublist l1 l2 -> Sublist l1 (x :: l2)
  | SublistTake : forall x l1 l2, Sublist l1 l2 -> Sublist (x :: l1) (x :: l2).

Lemma sublist_nil : forall {A : Type} (l : list A), Sublist l [] -> l = [].
Proof. intros A l H. inversion H. reflexivity. Qed.

Lemma sublist_metrics_le : forall f1 f2,
  Sublist f1 f2 -> fm_le (force_metrics f1) (force_metrics f2).
Proof.
  intros f1 f2 H.
  induction H as [l | x l1 l2 Hsub IH | x l1 l2 Hsub IH].
  - simpl. unfold fm_le.
    destruct (force_metrics l) as [c t e cl] eqn:Heq.
    simpl. repeat split; apply Nat.le_0_l.
  - simpl. unfold fm_le in *. destruct IH as [H1 [H2 [H3 H4]]].
    unfold metrics_add, unit_to_metrics. simpl.
    split; [lia|]. split; [lia|]. split; lia.
  - simpl. unfold fm_le in *. destruct IH as [H1 [H2 [H3 H4]]].
    unfold metrics_add, unit_to_metrics. simpl.
    split; [lia|]. split; [lia|]. split; lia.
Qed.

(** ** Section 10.5: Internal Respects External *)

Definition force_sublist (f1 f2 : Force) : Prop := Sublist f1 f2.

Theorem internal_respects_external : forall ext_res int_res,
  force_sublist (icand_force (int_winner int_res))
                (bid_force (ext_attacker_bid ext_res)) ->
  fm_le (icand_metrics (int_winner int_res))
        (bid_metrics (ext_attacker_bid ext_res)).
Proof.
  intros ext_res int_res Hsub.
  unfold icand_metrics, bid_metrics, force_sublist in *.
  apply sublist_metrics_le. exact Hsub.
Qed.

(** ** Section 10.6: Valid Bidding State Invariant *)

Definition valid_bidding_state (chal : BatchallChallenge) (resp : BatchallResponse)
                               (atk_bid def_bid : ForceBid) (hist : list ForceBid) : Prop :=
  bid_side atk_bid = Attacker /\
  bid_side def_bid = Defender /\
  fm_le (bid_metrics atk_bid) (force_metrics (chal_initial_force chal)) /\
  fm_le (bid_metrics def_bid) (force_metrics (resp_force resp)).

Lemma step_preserves_bid_validity : forall chal resp atk def hist ready action phase',
  valid_bidding_state chal resp atk def hist ->
  BatchallStep (PhaseBidding chal resp atk def hist ready) action phase' ->
  match phase' with
  | PhaseBidding _ _ atk' def' hist' _ => valid_bidding_state chal resp atk' def' hist'
  | _ => True
  end.
Proof.
  intros chal resp atk def hist ready action phase' Hvalid Hstep.
  inversion Hstep; subst; auto;
  unfold valid_bidding_state in *;
  destruct Hvalid as [Ha [Hd [Hale Hdle]]];
  repeat split; auto;
  unfold fm_lt, fm_le in *;
  try match goal with
  | [ H : _ /\ _ |- _ ] => destruct H as [[? [? [? ?]]] ?]
  end;
  repeat split; lia.
Qed.
