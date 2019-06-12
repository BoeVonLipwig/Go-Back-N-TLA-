------------------------------ MODULE Reciver ------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets

CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm reciver
variables sendReq = <<>>, reciveData = <<>>, requestNum = 0, output = <<>>;
fair process Recive = "recive"
begin
A:
    while TRUE do
        await reciveData # <<>>;
        if reciveData[1] # CORRUPT_DATA (* /\  rn = request number *)then
            if (reciveData[1] = requestNum) then
                output := output \o <<reciveData[2]>>;
                requestNum := requestNum + 1;
            end if;
        end if;
        reciveData := <<>>;
        sendReq := <<requestNum>>;
    end while;
end process;
end algorithm; 
*)
\* BEGIN TRANSLATION
VARIABLES sendReq, reciveData, requestNum, output

vars == << sendReq, reciveData, requestNum, output >>

ProcSet == {"recive"}

Init == (* Global variables *)
        /\ sendReq = <<>>
        /\ reciveData = <<>>
        /\ requestNum = 0
        /\ output = <<>>

Recive == /\ reciveData # <<>>
          /\ IF reciveData[1] # CORRUPT_DATA
                THEN /\ IF (reciveData[1] = requestNum)
                           THEN /\ output' = output \o <<reciveData[2]>>
                                /\ requestNum' = requestNum + 1
                           ELSE /\ TRUE
                                /\ UNCHANGED << requestNum, output >>
                ELSE /\ TRUE
                     /\ UNCHANGED << requestNum, output >>
          /\ reciveData' = <<>>
          /\ sendReq' = <<requestNum'>>

Next == Recive

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Recive)

\* END TRANSLATION
\* Checks that all variables remain in valid states

\*TypeOK == /\ \/ output = <<>>
\*             \/ \A i \in DOMAIN output : output[i] \in MESSAGE_TYPES
\*          /\ reciveData = <<>>
\*             \/ \A i \in DOMAIN reciveData : reciveData[i] \in MESSAGE_TYPES

          
          
Invariants == \*/\ TypeOK
              /\ requestNum < Len(MESSAGES)
              /\ requestNum > 0

Fairness == /\ WF_vars(Recive)


=============================================================================
\* Modification History
\* Last modified Wed Jun 12 12:46:58 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:49 NZST 2019 by sdmsi
