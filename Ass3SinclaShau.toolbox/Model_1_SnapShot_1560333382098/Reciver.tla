------------------------------ MODULE Reciver ------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets

CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm reciver
variables sendReq = <<>>, reciveData = <<>>, requestNum = 1, output = <<>>, state = "closed", synNum = -1;
fair process Recive = "recive"
begin
A:
    while TRUE do
        await reciveData # <<>> /\ state = "open";
        if reciveData[1] = "closing" then
            skip;
        end if;
        if reciveData[1] # CORRUPT_DATA then
            if (reciveData[1] = requestNum) then
                output := output \o <<reciveData[2]>>;
                requestNum := requestNum + 1;
            end if;
        reciveData := <<>>;
        sendReq := <<requestNum>>;
        end if;
    end while;
end process;

fair process WaitSYN = "waitsyn"
begin
A:
    while TRUE do
        await state = "closed" /\ reciveData # <<>>;
        if reciveData # CORRUPT_DATA then 
            if reciveData[1] = 1 /\ reciveData[2] = 0 then 
                synNum := reciveData[3] + 1;
                state := "SYN-RECIVED";
            else 
                reciveData := <<>>;
            end if;
        else 
            reciveData := <<>>;
        end if;
    end while;
end process;

fair process SendSYNACK = "sendsyn-ack"
begin
A:
    while TRUE do
        await state = "SYN-RECIVED" /\ reciveData # <<>>;
        if reciveData # CORRUPT_DATA then
            if Len(reciveData) = 4 /\ reciveData[1] = 0 /\ reciveData[2] = 1 /\ reciveData[3] = synNum /\ reciveData[4] = requestNum + 1 then
                state := "open";
            else 
                reciveData := <<>>;
            end if;
        else
            reciveData := <<>>;
        end if;
        
        if state = "SYN-RECIVED" then 
            sendReq := <<1, 1, synNum, requestNum>>
        end if;
    end while;
end process;

end algorithm; 
*)
\* BEGIN TRANSLATION
\* Label A of process Recive at line 10 col 5 changed to A_
\* Label A of process WaitSYN at line 29 col 5 changed to A_W
VARIABLES sendReq, reciveData, requestNum, output, state, synNum

vars == << sendReq, reciveData, requestNum, output, state, synNum >>

ProcSet == {"recive"} \cup {"waitsyn"} \cup {"sendsyn-ack"}

Init == (* Global variables *)
        /\ sendReq = <<>>
        /\ reciveData = <<>>
        /\ requestNum = 1
        /\ output = <<>>
        /\ state = "closed"
        /\ synNum = -1

Recive == /\ reciveData # <<>> /\ state = "open"
          /\ IF reciveData[1] = "closing"
                THEN /\ TRUE
                ELSE /\ TRUE
          /\ IF reciveData[1] # CORRUPT_DATA
                THEN /\ IF (reciveData[1] = requestNum)
                           THEN /\ output' = output \o <<reciveData[2]>>
                                /\ requestNum' = requestNum + 1
                           ELSE /\ TRUE
                                /\ UNCHANGED << requestNum, output >>
                     /\ reciveData' = <<>>
                     /\ sendReq' = <<requestNum'>>
                ELSE /\ TRUE
                     /\ UNCHANGED << sendReq, reciveData, requestNum, output >>
          /\ UNCHANGED << state, synNum >>

WaitSYN == /\ state = "closed" /\ reciveData # <<>>
           /\ IF reciveData # CORRUPT_DATA
                 THEN /\ IF reciveData[1] = 1 /\ reciveData[2] = 0
                            THEN /\ synNum' = reciveData[3] + 1
                                 /\ state' = "SYN-RECIVED"
                                 /\ UNCHANGED reciveData
                            ELSE /\ reciveData' = <<>>
                                 /\ UNCHANGED << state, synNum >>
                 ELSE /\ reciveData' = <<>>
                      /\ UNCHANGED << state, synNum >>
           /\ UNCHANGED << sendReq, requestNum, output >>

SendSYNACK == /\ state = "SYN-RECIVED" /\ reciveData # <<>>
              /\ IF reciveData # CORRUPT_DATA
                    THEN /\ IF Len(reciveData) = 4 /\ reciveData[1] = 0 /\ reciveData[2] = 1 /\ reciveData[3] = synNum /\ reciveData[4] = requestNum + 1
                               THEN /\ state' = "open"
                                    /\ UNCHANGED reciveData
                               ELSE /\ reciveData' = <<>>
                                    /\ state' = state
                    ELSE /\ reciveData' = <<>>
                         /\ state' = state
              /\ IF state' = "SYN-RECIVED"
                    THEN /\ sendReq' = <<1, 1, synNum, requestNum>>
                    ELSE /\ TRUE
                         /\ UNCHANGED sendReq
              /\ UNCHANGED << requestNum, output, synNum >>

Next == Recive \/ WaitSYN \/ SendSYNACK

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Recive)
        /\ WF_vars(WaitSYN)
        /\ WF_vars(SendSYNACK)

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
            /\ WF_vars(WaitSYN)
            /\ WF_vars(SendSYNACK)
 

=============================================================================
\* Modification History
\* Last modified Wed Jun 12 21:55:38 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:49 NZST 2019 by sdmsi
