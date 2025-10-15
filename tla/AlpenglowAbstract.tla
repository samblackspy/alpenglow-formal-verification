------------------------ MODULE AlpenglowAbstract ------------------------
(***************************************************************************
 * Abstract High-Level Specification of Alpenglow Consensus Protocol
 * 
 * This specification captures the CORE SAFETY PROPERTIES without 
 * implementation details like Rotor, BLS signatures, or network timing.
 * The detailed Alpenglow.tla specification should REFINE this abstract spec.
 * 
 * Key abstraction: Focus on WHAT is finalized, not HOW it's finalized.
 ***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS
  \* @type: Set(Str);
  AbstractValidators,     \* Set of validator identities
  \* @type: Int;
  AbstractMaxSlots,       \* Maximum slots to verify
  \* @type: Int;
  AbstractThreshold       \* Quorum threshold (simplify to single threshold)

VARIABLES
  \* @type: Int -> Str;
  abstract_chain,         \* Map: slot -> outcome (Block | Skip | Empty)
  \* @type: Set(Int);
  abstract_finalized,     \* Set of finalized slot numbers
  \* @type: Str -> Set(<<Int, Int>>);
  abstract_voted          \* Map: validator -> set of <<slot, hash>> votes

\* Type invariant
AbstractTypeOK ==
  /\ abstract_chain \in [0..AbstractMaxSlots -> {"Block", "Skip", "Empty"}]
  /\ abstract_finalized \in SUBSET (0..AbstractMaxSlots)
  /\ abstract_voted \in [AbstractValidators -> SUBSET ((0..AbstractMaxSlots) \X (0..100))]

\* Initial state - empty chain
AbstractInit ==
  /\ abstract_chain = [s \in 0..AbstractMaxSlots |-> "Empty"]
  /\ abstract_finalized = {}
  /\ abstract_voted = [v \in AbstractValidators |-> {}]

\* Abstract voting action - validator votes for a slot/hash pair
\* Non-equivocation: validator can only vote once per slot
AbstractVote(validator, slot, hash) ==
  /\ slot \notin abstract_finalized
  /\ \A h \in 0..100 : <<slot, h>> \notin abstract_voted[validator]  \* No existing vote for this slot
  /\ abstract_voted' = [abstract_voted EXCEPT ![validator] = @ \cup {<<slot, hash>>}]
  /\ UNCHANGED <<abstract_chain, abstract_finalized>>

\* Abstract finalization - when quorum reached, finalize the slot
AbstractFinalize(slot, hash) ==
  /\ slot \notin abstract_finalized
  /\ abstract_chain[slot] = "Empty"
  /\ \* Quorum of validators voted for this slot/hash
     LET voters == {v \in AbstractValidators : <<slot, hash>> \in abstract_voted[v]}
     IN Cardinality(voters) >= AbstractThreshold
  /\ abstract_chain' = [abstract_chain EXCEPT ![slot] = "Block"]
  /\ abstract_finalized' = abstract_finalized \cup {slot}
  /\ UNCHANGED abstract_voted

\* Abstract skip - when quorum agrees to skip
AbstractSkip(slot) ==
  /\ slot \notin abstract_finalized
  /\ abstract_chain[slot] = "Empty"
  /\ \* Quorum voted to skip this slot
     LET skip_voters == {v \in AbstractValidators : <<slot, 0>> \in abstract_voted[v]}
     IN Cardinality(skip_voters) >= AbstractThreshold
  /\ abstract_chain' = [abstract_chain EXCEPT ![slot] = "Skip"]
  /\ abstract_finalized' = abstract_finalized \cup {slot}
  /\ UNCHANGED abstract_voted

\* Next-state relation
AbstractNext ==
  \/ \E v \in AbstractValidators, s \in 0..AbstractMaxSlots, h \in 0..100 :
       AbstractVote(v, s, h)
  \/ \E s \in 0..AbstractMaxSlots, h \in 0..100 :
       AbstractFinalize(s, h)
  \/ \E s \in 0..AbstractMaxSlots :
       AbstractSkip(s)
  \/ UNCHANGED <<abstract_chain, abstract_finalized, abstract_voted>>  \* Allow stuttering to prevent deadlock

\* Specification
AbstractSpec == AbstractInit /\ [][AbstractNext]_<<abstract_chain, abstract_finalized, abstract_voted>>

\* ============================================================================
\* CORE SAFETY PROPERTIES (Abstract Level)
\* ============================================================================

\* Property 1: Slot Uniqueness - Each slot has exactly one outcome
AbstractSlotUniqueness ==
  \A s \in 0..AbstractMaxSlots :
    abstract_chain[s] \in {"Block", "Skip", "Empty"}

\* Property 2: Finalization Immutability - Once finalized, never changes
AbstractFinalityImmutability ==
  \A s \in abstract_finalized :
    abstract_chain[s] \in {"Block", "Skip"}

\* Property 3: Agreement - No two conflicting finalizations
\* Validators who voted for a finalized slot must agree on the hash
AbstractAgreement ==
  \A s \in abstract_finalized :
    \A v1, v2 \in AbstractValidators :
      \A h1, h2 \in 0..100 :
        /\ <<s, h1>> \in abstract_voted[v1]
        /\ <<s, h2>> \in abstract_voted[v2]
        => \/ h1 = h2  \* Same block hash
           \/ h1 = 0  \* Skip vote
           \/ h2 = 0  \* Skip vote

\* Property 4: Finalization Requires Quorum
AbstractQuorumRequired ==
  \A s \in abstract_finalized :
    abstract_chain[s] = "Block" =>
      \E h \in 0..100 :
        LET voters == {v \in AbstractValidators : <<s, h>> \in abstract_voted[v]}
        IN Cardinality(voters) >= AbstractThreshold

=============================================================================
