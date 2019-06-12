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

fair process Send = "send"
begin
A:
    while TRUE do
        await sendReq = <<>>;
        sendReq := <<requestNum>>;
    end while;
end process;
end algorithm; 
*)
\* BEGIN TRANSLATION
\* Label A of process Recive at line 10 col 5 changed to A_
VARIABLES sendReq, reciveData, requestNum, output

vars == << sendReq, reciveData, requestNum, output >>

ProcSet == {"recive"} \cup {"send"}

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

Send == /\ sendReq = <<>>
        /\ sendReq' = <<requestNum>>
        /\ UNCHANGED << reciveData, requestNum, output >>

Next == Recive \/ Send

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Recive)
        /\ WF_vars(Send)

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
\* Last modified Tue Jun 11 16:31:56 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:49 NZST 2019 by sdmsi
