------------------------------ MODULE Reciver ------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets

CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm reciver
variables sendReq = <<>>, reciveData = <<>>, requestNum = 1, output = <<>>, state = "closed", synNum = 0;
fair process Recive = "recive"
begin
A:
    while TRUE do
        await reciveData # <<>> /\ state = "open";
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

fair process connect = "connect"
begin
A:
    while TRUE do
        await state # "open" /\ state # "closing" /\ reciveData # <<>> /\ (Len(reciveData) = 3\/Len(reciveData) = 4);
        if Len(reciveData) = 3 /\ (state = "closed" \/ state = "SYN-RECIVED")  then
            if reciveData[1] = 1 /\ reciveData[2] = 0 then 
                sendReq := <<1,1, reciveData[3] + 1, requestNum>>;
                synNum := reciveData[3] + 1;
                state := "SYN-RECIVED"
            end if;
        elsif Len(reciveData) = 4 /\ state = "SYN-RECIVED" then
            if reciveData[1] = 0 /\ reciveData[2] = 1 /\ reciveData[3] = synNum /\ reciveData[4] = requestNum + 1 then
                state := "open";
            else
                sendReq := <<1,1, reciveData[3] + 1, requestNum>>;
            end if;
        end if;
    end while;
end process;

end algorithm; 
*)
\* BEGIN TRANSLATION
\* Label A of process Recive at line 10 col 5 changed to A_
VARIABLES sendReq, reciveData, requestNum, output, state, synNum

vars == << sendReq, reciveData, requestNum, output, state, synNum >>

ProcSet == {"recive"} \cup {"connect"}

Init == (* Global variables *)
        /\ sendReq = <<>>
        /\ reciveData = <<>>
        /\ requestNum = 1
        /\ output = <<>>
        /\ state = "closed"
        /\ synNum = 0

Recive == /\ reciveData # <<>> /\ state = "open"
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

connect == /\ state # "open" /\ state # "closing" /\ reciveData # <<>> /\ (Len(reciveData) = 3\/Len(reciveData) = 4)
           /\ IF Len(reciveData) = 3 /\ (state = "closed" \/ state = "SYN-RECIVED")
                 THEN /\ IF reciveData[1] = 1 /\ reciveData[2] = 0
                            THEN /\ sendReq' = <<1,1, reciveData[3] + 1, requestNum>>
                                 /\ synNum' = reciveData[3] + 1
                                 /\ state' = "SYN-RECIVED"
                            ELSE /\ TRUE
                                 /\ UNCHANGED << sendReq, state, synNum >>
                 ELSE /\ IF Len(reciveData) = 4 /\ state = "SYN-RECIVED"
                            THEN /\ IF reciveData[1] = 0 /\ reciveData[2] = 1 /\ reciveData[3] = synNum /\ reciveData[4] = requestNum + 1
                                       THEN /\ state' = "open"
                                            /\ UNCHANGED sendReq
                                       ELSE /\ sendReq' = <<1,1, reciveData[3] + 1, requestNum>>
                                            /\ state' = state
                            ELSE /\ TRUE
                                 /\ UNCHANGED << sendReq, state >>
                      /\ UNCHANGED synNum
           /\ UNCHANGED << reciveData, requestNum, output >>

Next == Recive \/ connect

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Recive)
        /\ WF_vars(connect)

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
\* Last modified Wed Jun 12 20:23:01 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:49 NZST 2019 by sdmsi
