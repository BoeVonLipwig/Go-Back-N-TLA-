------------------------------- MODULE Sender -------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets
CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm sender
variables sendData = <<>>, receiveReq = <<>>, state = "Opening", 
sequenceNum = 1, windowStart = 1, windowEnd = WINDOW_SIZE+1, reqNum = -1;

\* this is a little method used for finding the minimum of two intgers
\* it is used when assigning a value to windowEnd to make sure it never overshoots the maximum size of the message
define
    MIN(x,y)  == IF (x < y) THEN x ELSE y 
end define; 

(* This is the main process, it sends all of the messages, 
   mannages the sliding window and initiates the termination process*)
fair process Send = "send"
begin
A:
(*When the wire is empty and there is data to send, send the data*)
    while TRUE do 
        \* this line makes sure that the following code is only exicuted when the connection is active
        await state = "Open" /\ (sendData = <<>> \/ receiveReq # <<>>);
        \* this line checks for corrupt data
        if receiveReq # <<>> /\ receiveReq[1] # CORRUPT_DATA then 
            \* This statment checks if we have finished sending all our data and if so starts the termination process
            if receiveReq[1] = Len(MESSAGES) + 1 then 
                state := "SENDING_FIN";
            \* this statment moves the window foward when we get confimation of data recived
            elsif receiveReq[1] > windowStart then
                windowEnd := MIN(WINDOW_SIZE + receiveReq[1], Len(MESSAGES));
                windowStart := receiveReq[1];
            end if;
        end if;
        receiveReq := <<>>; 
        \*This section sends the data and updates the sequence number as nessacary
        if sendData = <<>> /\ MESSAGES # <<>> /\ sequenceNum < Len(MESSAGES) + 1 /\ state # "closing" then
            sendData := <<sequenceNum, MESSAGES[sequenceNum]>>;
            if sequenceNum < windowEnd /\ sequenceNum > windowStart - 1 then
                sequenceNum := sequenceNum + 1;
            else
                \* resets sequence number to start of window once it reaches the end
                sequenceNum := windowStart;
            end if;
        end if;
        
    end while;
end process;

(* This is the starting process, it ititlises the connection with the reciver
   by sening a SYN command which starts the 3 way hand shake required to set 
   up the starting connection *)
fair process SYN = "syn" 
begin
A:
    while TRUE do
        \* this can only trigger in the starting state 
        await state = "Opening" /\ sendData = <<>>;
        (* this line checks the reply to our SYN message and if it is SYN-ACK 
           then it changes the state which pushes us into the ACk sending state*)
           \* check that a message has been recived and that it is not corrupted
        if receiveReq # <<>> /\ receiveReq # CORRUPT_DATA then
            \* this line check that the message recived is SYN-ACK and that the ISN has been incremneted
            if receiveReq[1] = 1 /\ receiveReq[2] = 1 /\ receiveReq[3] = sequenceNum + 1 then 
                reqNum := receiveReq[4] + 1; 
                state := "SYN_ACK_RECEIVED";
            end if;
            receiveReq := <<>>;
        end if; 
        
        \* spam SYN constantly until successful 
        if state = "Opening" then
            \* sends the syn message along with the ISN
            sendData := <<1, 0, sequenceNum>>;
        end if; 
        
    end while;

end process;

fair process ACK = "ack"
begin 
A: 
    while TRUE do  
        await state = "SYN_ACK_RECEIVED";
        \*wait for real data
        if receiveReq # <<>> /\ receiveReq # CORRUPT_DATA then 
                if Len(receiveReq) = 1 /\ receiveReq[1] = reqNum -1 then 
                    state := "Open"
                else  
                    receiveReq := <<>>;
                end if;
            else 
                receiveReq := <<>>;
       end if;
       \* spam ACK
       if state = "SYN_ACK_RECEIVED" then 
           sendData := <<0, 1, sequenceNum + 1, reqNum>>;
       end if;
    end while; 
end process;

fair process FIN = "fin"
begin 
A: 
    while TRUE do 
        await state = "SENDING_FIN";
        if receiveReq # <<>> then 
            if receiveReq # CORRUPT_DATA then
                if receiveReq[1] = -2 /\ receiveReq[2] = "FIN-ACK" then 
                    state := "RECEIVED_FIN-ACK";
                end if;
            end if;
        end if; 
        receiveReq := <<>>;
        
        \* repeatedly send the fin command to start the 3 way termination handshake
        if state = "SENDING_FIN" then
            sendData := <<-1, "FIN">>; 
        end if;
    end while;
end process; 

\* This process send the final ACK to acknolage the terminating of the connection, 
\* it can nevre stop doing this as normally it would use a timeout syste and tla 
\* does not have that functionality
fair process FINACK = "finack"
begin 
A: 
    while TRUE do  
        await (state = "RECEIVED_FIN-ACK" \/ state = "Closed");
        
        (* since we cant prove this message has been received by the sender and we cant time this out 
           we will just send it forever as tla does not allow us to fully implement tcp*)
         
        state := "Closed";  
        sendData := <<-3, "ACK">>;
    end while; 
end process;


end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process Send at line 20 col 5 changed to A_
\* Label A of process SYN at line 55 col 5 changed to A_S
\* Label A of process ACK at line 83 col 5 changed to A_A
\* Label A of process FIN at line 107 col 5 changed to A_F
VARIABLES sendData, receiveReq, state, sequenceNum, windowStart, windowEnd, 
          reqNum

(* define statement *)
MIN(x,y)  == IF (x < y) THEN x ELSE y


vars == << sendData, receiveReq, state, sequenceNum, windowStart, windowEnd, 
           reqNum >>

ProcSet == {"send"} \cup {"syn"} \cup {"ack"} \cup {"fin"} \cup {"finack"}

Init == (* Global variables *)
        /\ sendData = <<>>
        /\ receiveReq = <<>>
        /\ state = "Opening"
        /\ sequenceNum = 1
        /\ windowStart = 1
        /\ windowEnd = WINDOW_SIZE+1
        /\ reqNum = -1

Send == /\ state = "Open" /\ (sendData = <<>> \/ receiveReq # <<>>)
        /\ IF receiveReq # <<>> /\ receiveReq[1] # CORRUPT_DATA
              THEN /\ IF receiveReq[1] = Len(MESSAGES) + 1
                         THEN /\ state' = "SENDING_FIN"
                              /\ UNCHANGED << windowStart, windowEnd >>
                         ELSE /\ IF receiveReq[1] > windowStart
                                    THEN /\ windowEnd' = MIN(WINDOW_SIZE + receiveReq[1], Len(MESSAGES))
                                         /\ windowStart' = receiveReq[1]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << windowStart, 
                                                         windowEnd >>
                              /\ state' = state
              ELSE /\ TRUE
                   /\ UNCHANGED << state, windowStart, windowEnd >>
        /\ receiveReq' = <<>>
        /\ IF sendData = <<>> /\ MESSAGES # <<>> /\ sequenceNum < Len(MESSAGES) + 1 /\ state' # "closing"
              THEN /\ sendData' = <<sequenceNum, MESSAGES[sequenceNum]>>
                   /\ IF sequenceNum < windowEnd' /\ sequenceNum > windowStart' - 1
                         THEN /\ sequenceNum' = sequenceNum + 1
                         ELSE /\ sequenceNum' = windowStart'
              ELSE /\ TRUE
                   /\ UNCHANGED << sendData, sequenceNum >>
        /\ UNCHANGED reqNum

SYN == /\ state = "Opening" /\ sendData = <<>>
       /\ IF receiveReq # <<>> /\ receiveReq # CORRUPT_DATA
             THEN /\ IF receiveReq[1] = 1 /\ receiveReq[2] = 1 /\ receiveReq[3] = sequenceNum + 1
                        THEN /\ reqNum' = receiveReq[4] + 1
                             /\ state' = "SYN_ACK_RECEIVED"
                        ELSE /\ TRUE
                             /\ UNCHANGED << state, reqNum >>
                  /\ receiveReq' = <<>>
             ELSE /\ TRUE
                  /\ UNCHANGED << receiveReq, state, reqNum >>
       /\ IF state' = "Opening"
             THEN /\ sendData' = <<1, 0, sequenceNum>>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd >>

ACK == /\ state = "SYN_ACK_RECEIVED"
       /\ IF receiveReq # <<>>
             THEN /\ IF receiveReq # CORRUPT_DATA
                        THEN /\ IF Len(receiveReq) = 1 /\ receiveReq[1] = reqNum -1
                                   THEN /\ state' = "Open"
                                        /\ UNCHANGED receiveReq
                                   ELSE /\ receiveReq' = <<>>
                                        /\ state' = state
                        ELSE /\ receiveReq' = <<>>
                             /\ state' = state
             ELSE /\ TRUE
                  /\ UNCHANGED << receiveReq, state >>
       /\ IF state' = "SYN_ACK_RECEIVED"
             THEN /\ sendData' = <<0, 1, sequenceNum + 1, reqNum>>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd, reqNum >>

FIN == /\ state = "SENDING_FIN"
       /\ IF receiveReq # <<>>
             THEN /\ IF receiveReq # CORRUPT_DATA
                        THEN /\ IF receiveReq[1] = -2 /\ receiveReq[2] = "FIN-ACK"
                                   THEN /\ state' = "RECEIVED_FIN-ACK"
                                   ELSE /\ TRUE
                                        /\ state' = state
                        ELSE /\ TRUE
                             /\ state' = state
             ELSE /\ TRUE
                  /\ state' = state
       /\ receiveReq' = <<>>
       /\ IF state' = "SENDING_FIN"
             THEN /\ sendData' = <<-1, "FIN">>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd, reqNum >>

FINACK == /\ (state = "RECEIVED_FIN-ACK" \/ state = "Closed")
          /\ state' = "Closed"
          /\ sendData' = <<-3, "ACK">>
          /\ UNCHANGED << receiveReq, sequenceNum, windowStart, windowEnd, 
                          reqNum >>

Next == Send \/ SYN \/ ACK \/ FIN \/ FINACK

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Send)
        /\ WF_vars(SYN)
        /\ WF_vars(ACK)
        /\ WF_vars(FIN)
        /\ WF_vars(FINACK)

\* END TRANSLATION

\* checks that the message we are trying to send is of the correcdt type
             
WinStrOK == /\ windowStart < Len(MESSAGES) + 1 

WinEndOK == /\ windowEnd < Len(MESSAGES) + 1 
            /\ windowEnd = windowStart + WINDOW_SIZE
            
SeqNumOK == /\ sequenceNum > 0
            /\ sequenceNum > windowStart - 1 
            /\ sequenceNum < windowEnd 
            /\ sequenceNum < Len(MESSAGES) + 1 

Invariants == /\ WinStrOK
              /\ WinEndOK
              /\ SeqNumOK

Properties == \A x \in {"RECEIVED_FIN-ACK", "SYN_ACK_RECEIVED", "Open", "Opening", "Closed", "SENDING_FIN" }: <>( state = x )
              


\* Both of the below proccesses are weakly fair
Fairness == /\ WF_vars(Send)
            /\ WF_vars(SYN)
            /\ WF_vars(ACK)
            /\ WF_vars(FIN)
            /\ WF_vars(FINACK)
=============================================================================
\* Modification History
\* Last modified Thu Jun 13 02:44:07 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:39 NZST 2019 by sdmsi
