------------------------------ MODULE DataWire ------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets
CONSTANTS CORRUPT_DATA, MESSAGE_TYPES

(* --algorithm dataWire
variables outputW = <<>>, inputW = <<>>;

fair+ process Transfer = "transfer"
begin
    A:
    while TRUE do
        (*If the is a message send it*)
        await inputW # <<>> /\ outputW = <<>>;
        outputW := inputW; \* Send
        inputW := <<>>; 
    end while;

end process;

process Courrpt = "Courrpt"
begin
    A:
    while TRUE do
        (*when there is an input corrupt it and send it on*)
        await inputW # <<>> /\ outputW = <<>>;
        outputW := <<CORRUPT_DATA>>;
        inputW := <<>>; 
    end while;

end process;
        
        
process Drop = "drop"
begin
    A:
    while TRUE do
        (*when there is an input clear it and send nothing*)
        await inputW # <<>> /\ outputW = <<>>;
        outputW := <<>>;
        inputW := <<>>; 
    end while;

end process;
end algorithm; 

*)
\* BEGIN TRANSLATION
\* Label A of process Transfer at line 11 col 5 changed to A_
\* Label A of process Courrpt at line 23 col 5 changed to A_C
VARIABLES outputW, inputW

vars == << outputW, inputW >>

ProcSet == {"transfer"} \cup {"Courrpt"} \cup {"drop"}

Init == (* Global variables *)
        /\ outputW = <<>>
        /\ inputW = <<>>

Transfer == /\ inputW # <<>> /\ outputW = <<>>
            /\ outputW' = inputW
            /\ inputW' = <<>>

Courrpt == /\ inputW # <<>> /\ outputW = <<>>
           /\ outputW' = <<CORRUPT_DATA>>
           /\ inputW' = <<>>

Drop == /\ inputW # <<>> /\ outputW = <<>>
        /\ outputW' = <<>>
        /\ inputW' = <<>>

Next == Transfer \/ Courrpt \/ Drop

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(Transfer)

\* END TRANSLATION

\* Transfer is strongly fair
Fairness == /\ SF_vars(Transfer)

\* This has been directly coppied from abp assignment 2
=============================================================================
\* Modification History
\* Last modified Thu Jun 13 02:24:41 NZST 2019 by sdmsi
\* Last modified Sun May 19 20:08:04 NZST 2019 by sinclashau
\* Last modified Sun May 19 19:25:11 NZST 2019 by sinclashau
\* Last modified Sun May 19 19:24:52 NZST 2019 by sinclashau
\* Last modified Sun May 19 19:21:34 NZST 2019 by sinclashau
\* Last modified Fri May 17 17:29:14 NZST 2019 by sinclashau
\* Last modified Tue May 14 18:55:25 NZST 2019 by sinclashau
\* Created Thu May 09 13:14:38 NZST 2019 by Shaun
