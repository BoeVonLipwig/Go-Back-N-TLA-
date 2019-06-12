------------------------------ MODULE Receiver ------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets

CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm receiver
variables sendReq = <<>>, receiveData = <<>>, requestNum = 1, output = <<>>, state = "Waiting", synNum = -1;

(* this precess is responceable for reciving all the data from sender, 
   processing it and adding it to the output. It then sends a equest for 
   the next bit of data, confiming that it processed the last one*)
fair process Receive = "receive"
begin
A:
    while TRUE do
    \* wait till data is recived
        await receiveData # <<>> /\ state = "Open";
        if receiveData[1] # CORRUPT_DATA then
            \* sender will send FIN if it wants to close the connection and this wil start the 3 way handshake to terminate the connection
            if receiveData[1] = -1 /\ receiveData[2] = "FIN" then
                state := "FIN_RECEIVED";
            \* is the data recived is the data we want then increment our request number and and the data to output
            elsif (receiveData[1] = requestNum) then
                output := output \o <<receiveData[2]>>;
                requestNum := requestNum + 1;
            end if;
            \* send a request for the next bit of data
            sendReq := <<requestNum>>;
        end if;
        receiveData := <<>>;
    end while;
    
end process;

(* This is the starting process for recever, it waits for a handshake to be started
   and if one is attempted it checks it and starts the SYN-ACK process*)
fair process WaitSYN = "waitsyn"
begin
A:
    while TRUE do
    \* only starts if data is received
        await state = "Waiting" /\ receiveData # <<>>;
        \* if the message is an elligable SYN the change the sate for a reply
        if receiveData # CORRUPT_DATA /\ receiveData[1] = 1 /\ receiveData[2] = 0 then 
            synNum := receiveData[3] + 1;
            state := "SYN_RECEIVED";
        \* otherwise clear it and wait for a better one
        else 
            receiveData := <<>>;
        end if;
    end while;
end process;

(*This process sends the SYN-ACK messages and waits for the sender to send a ACK*)
fair process SendSYNACK = "sendsyn-ack"
begin
A:
    while TRUE do
        await state = "SYN_RECEIVED" /\ receiveData # <<>>;
        \* if a valid ACK command with the ISN incremented is sent then start waiting for data
        if receiveData # CORRUPT_DATA /\ Len(receiveData) = 4 /\ receiveData[1] = 0 /\ receiveData[2] = 1 /\ receiveData[3] = synNum /\ receiveData[4] = requestNum + 1 then
            state := "WAIT-FOR-DATA";
        end if;
        receiveData := <<>>;
        
        \* spam the SYN-ACK message to the sender with tis ISN incremented and our own ISN for it to increment
        if state = "SYN_RECEIVED" then
            sendReq := <<1, 1, synNum, requestNum>>;
        end if;
    end while;
end process;

(*This process waits for data and when it confims that it has recived some starts the reciv process*)
fair process WaitData = "waitdata"
begin 
A: 
    while TRUE do
        await receiveData # <<>> /\ state = "WAIT-FOR-DATA";
        \* if we get data with the correct requestNum(alway 1 in this case) then set the state to open which will trigger the recice process
        if receiveData # CORRUPT_DATA /\ receiveData[1] = requestNum then
            state := "Open";
        end if;
        \* spam a request for the first bit of data to the sender until we get it
        if state = "WAIT-FOR-DATA" then 
            sendReq := <<requestNum>>;
            receiveData := <<>>;
        end if
    end while;
end process;

(* This is part of the connection termination, when a FIN is sent this
   process is triggered and it wends the FIN-ACK until it recives a ACK
   and then it considers the connection over and closes down*) 
fair process SendFINACK = "sendfinack"
begin
A: 
    while TRUE do
        
        await receiveData # <<>> /\ state = "FIN_RECEIVED";
        \* if a ACK is recived then shut down, could probably go back to the waiting state if i wanted
        if receiveData # CORRUPT_DATA /\ receiveData[1] = -3 /\ receiveData[2] = "ACK" then
            state := "Closed";
        end if;
        receiveData := <<>>;
        
        \* spam out the FIN-ACK acknolagement of the attempt to terminate the connection
        if state = "FIN_RECEIVED" then 
            sendReq := <<-2, "FIN-ACK">>;
        end if;
    end while;

end process;

end algorithm; 
*)
\* BEGIN TRANSLATION
\* Label A of process Receive at line 10 col 5 changed to A_
\* Label A of process WaitSYN at line 30 col 5 changed to A_W
\* Label A of process SendSYNACK at line 48 col 5 changed to A_S
\* Label A of process WaitData at line 68 col 5 changed to A_Wa
VARIABLES sendReq, receiveData, requestNum, output, state, synNum

vars == << sendReq, receiveData, requestNum, output, state, synNum >>

ProcSet == {"receive"} \cup {"waitsyn"} \cup {"sendsyn-ack"} \cup {"waitdata"} \cup {"sendfinack"}

Init == (* Global variables *)
        /\ sendReq = <<>>
        /\ receiveData = <<>>
        /\ requestNum = 1
        /\ output = <<>>
        /\ state = "Waiting"
        /\ synNum = -1

Receive == /\ receiveData # <<>> /\ state = "Open"
           /\ IF receiveData[1] # CORRUPT_DATA
                 THEN /\ IF receiveData[1] = -1 /\ receiveData[2] = "FIN"
                            THEN /\ state' = "FIN_RECEIVED"
                                 /\ UNCHANGED << requestNum, output >>
                            ELSE /\ IF (receiveData[1] = requestNum)
                                       THEN /\ output' = output \o <<receiveData[2]>>
                                            /\ requestNum' = requestNum + 1
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << requestNum, output >>
                                 /\ state' = state
                      /\ sendReq' = <<requestNum'>>
                 ELSE /\ TRUE
                      /\ UNCHANGED << sendReq, requestNum, output, state >>
           /\ receiveData' = <<>>
           /\ UNCHANGED synNum

WaitSYN == /\ state = "Waiting" /\ receiveData # <<>>
           /\ IF receiveData # CORRUPT_DATA
                 THEN /\ IF receiveData[1] = 1 /\ receiveData[2] = 0
                            THEN /\ synNum' = receiveData[3] + 1
                                 /\ state' = "SYN_RECEIVED"
                                 /\ UNCHANGED receiveData
                            ELSE /\ receiveData' = <<>>
                                 /\ UNCHANGED << state, synNum >>
                 ELSE /\ receiveData' = <<>>
                      /\ UNCHANGED << state, synNum >>
           /\ UNCHANGED << sendReq, requestNum, output >>

SendSYNACK == /\ state = "SYN_RECEIVED" /\ receiveData # <<>>
              /\ IF receiveData # CORRUPT_DATA
                    THEN /\ IF Len(receiveData) = 4 /\ receiveData[1] = 0 /\ receiveData[2] = 1 /\ receiveData[3] = synNum /\ receiveData[4] = requestNum + 1
                               THEN /\ state' = "WAIT-FOR-DATA"
                               ELSE /\ TRUE
                                    /\ state' = state
                         /\ receiveData' = <<>>
                    ELSE /\ receiveData' = <<>>
                         /\ state' = state
              /\ IF state' = "SYN_RECEIVED"
                    THEN /\ sendReq' = <<1, 1, synNum, requestNum>>
                    ELSE /\ TRUE
                         /\ UNCHANGED sendReq
              /\ UNCHANGED << requestNum, output, synNum >>

WaitData == /\ receiveData # <<>> /\ state = "WAIT-FOR-DATA"
            /\ IF receiveData # CORRUPT_DATA
                  THEN /\ IF receiveData[1] = requestNum
                             THEN /\ state' = "Open"
                             ELSE /\ TRUE
                                  /\ state' = state
                  ELSE /\ TRUE
                       /\ state' = state
            /\ IF state' = "WAIT-FOR-DATA"
                  THEN /\ sendReq' = <<requestNum>>
                       /\ receiveData' = <<>>
                  ELSE /\ TRUE
                       /\ UNCHANGED << sendReq, receiveData >>
            /\ UNCHANGED << requestNum, output, synNum >>

SendFINACK == /\ receiveData # <<>> /\ state = "FIN_RECEIVED"
              /\ IF receiveData # CORRUPT_DATA
                    THEN /\ IF receiveData[1] = -3 /\ receiveData[2] = "ACK"
                               THEN /\ state' = "Closed"
                               ELSE /\ TRUE
                                    /\ state' = state
                    ELSE /\ TRUE
                         /\ state' = state
              /\ receiveData' = <<>>
              /\ IF state' = "FIN_RECEIVED"
                    THEN /\ sendReq' = <<-2, "FIN-ACK">>
                    ELSE /\ TRUE
                         /\ UNCHANGED sendReq
              /\ UNCHANGED << requestNum, output, synNum >>

Next == Receive \/ WaitSYN \/ SendSYNACK \/ WaitData \/ SendFINACK

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Receive)
        /\ WF_vars(WaitSYN)
        /\ WF_vars(SendSYNACK)
        /\ WF_vars(WaitData)
        /\ WF_vars(SendFINACK)

\* END TRANSLATION
\* Checks that all variables remain in valid states
          
Invariants == /\ requestNum < Len(MESSAGES)
              /\ requestNum > 0

Fairness == /\ WF_vars(Receive)
            /\ WF_vars(WaitSYN)
            /\ WF_vars(SendSYNACK)
            /\ WF_vars(WaitData)
            /\ WF_vars(SendFINACK)
            
            
            
Properties == \A x \in {"Closed", "FIN_RECEIVED","SYN_RECEIVED", "WAIT-FOR-DATA", "Open", "Waiting"}: <>( state = x )

=============================================================================
\* Modification History
\* Last modified Thu Jun 13 03:09:59 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:49 NZST 2019 by sdmsi
