----    Utilities

Load "Util.tlv";  -- Utility routines (arrays).
Load "TS.tlv";

----    Model Checking

-- The following three modules depend on each other.
Load "MCTL.tlv";     -- Model Check Linear Temporal Logic.
Load "MCTLS.tlv";    -- Model Check CTL STAR.
Load "TESTER.tlv";   -- Create testers from specifications, for model checking.

Load "ctl_fair.tlv"; -- ctl with fairness .

Load "MCsimple.tlv"; -- Special model checking routines

----    Simulations

Load "SIMULATE.tlv"; -- Simulations.
Load "TLSIMU.tlv";   -- Annotate simulations with temporal logic.

----    Deductive

Load "Floyd.tlv";    -- Floyd Invariance.

Load "Abstract.tlv"; -- Prove refinement.

-- binv, inv, isvalid, invx
Load "deductive.tlv";

Load "compat.tlv";

Run init_TS;
-- Run init_compat;
