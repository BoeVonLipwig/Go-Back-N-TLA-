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
        either outputW := inputW; \* Send
        or  outputW := <<CORRUPT_DATA>>;
        or outputW := <<>>;
        end either;
        inputW := <<>>; 
    end while;

end process;

\*process Courrpt = "Courrpt"
\*begin
\*    A:
\*    while TRUE do
\*        (*when there is an input corrupt it and send it on*)
\*        await inputW # <<>> /\ outputW = <<>>;
\*        outputW := <<CORRUPT_DATA>>;
\*        inputW := <<>>; 
\*    end while;
\*
\*end process;
\*        
\*        
\*process Drop = "drop"
\*begin
\*    A:
\*    while TRUE do
\*        (*when there is an input clear it and send nothing*)
\*        await inputW # <<>> /\ outputW = <<>>;
\*        outputW := <<>>;
\*        inputW := <<>>; 
\*    end while;
\*
\*end process;
end algorithm; 

*)
\* BEGIN TRANSLATION
VARIABLES outputW, inputW

vars == << outputW, inputW >>

ProcSet == {"transfer"}

Init == (* Global variables *)
        /\ outputW = <<>>
        /\ inputW = <<>>

Transfer == /\ inputW # <<>> /\ outputW = <<>>
            /\ \/ /\ outputW' = inputW
               \/ /\ outputW' = <<CORRUPT_DATA>>
               \/ /\ outputW' = <<>>
            /\ inputW' = <<>>

Next == Transfer

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(Transfer)

\* END TRANSLATION

\* Transfer is strongly fair
Fairness == /\ SF_vars(Transfer)

\* This has been directly coppied from abp assignment 2
=============================================================================
\* Modification History
\* Last modified Thu Jun 13 02:24:00 NZST 2019 by sdmsi
\* Last modified Sun May 19 20:08:04 NZST 2019 by sinclashau
\* Last modified Sun May 19 19:25:11 NZST 2019 by sinclashau
\* Last modified Sun May 19 19:24:52 NZST 2019 by sinclashau
\* Last modified Sun May 19 19:21:34 NZST 2019 by sinclashau
\* Last modified Fri May 17 17:29:14 NZST 2019 by sinclashau
\* Last modified Tue May 14 18:55:25 NZST 2019 by sinclashau
\* Created Thu May 09 13:14:38 NZST 2019 by Shaun
