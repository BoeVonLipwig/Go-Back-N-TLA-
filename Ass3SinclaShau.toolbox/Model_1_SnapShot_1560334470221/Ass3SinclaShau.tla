--------------------------- MODULE Ass3SinclaShau ---------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets

CONSTANT  CORRUPT_DATA,
          WINDOW_SIZE,
          MESSAGES(*is the input message to send*), 
          MESSAGE_TYPES(*used to typecheck that the message of the right type*)  \* to be set in model

VARIABLES sendDataQueue, \* send data  to dataWire
          receiveDataQueue,     \* receive data from dataWire
          receiveReqQueue,
          sendReqQueue,
          requestNum, \*
          sequenceNum, \*
          windowStart, \*
          windowEnd, \* 
          mess,                 \* message input to  sender process
          messOut,
          senderState,
          reciverState,
          synNum,
          reqNum
           
          
          

vars == <<sendDataQueue, receiveDataQueue, receiveReqQueue, sendReqQueue, requestNum, sequenceNum, windowStart, windowEnd, mess, messOut, senderState, reciverState, synNum, reqNum>>
 
dataWir == INSTANCE DataWire WITH inputW <- sendDataQueue, outputW <- receiveDataQueue
reqWir == INSTANCE DataWire WITH inputW <- sendReqQueue, outputW <- receiveReqQueue
sender == INSTANCE Sender WITH sendData <- sendDataQueue, reciveReq <- receiveReqQueue, toSend <- mess, state <- senderState
reciver == INSTANCE Reciver WITH sendReq <- sendReqQueue, reciveData <- receiveDataQueue, output <- messOut, state <- reciverState


\* The following varibles run the init code in their respective modules
Init ==  /\ dataWir!Init
         /\ reqWir!Init
         /\ sender!Init
         /\ reciver!Init


\* These are used to help define what the "next" step is and state what variables remain unchanged
dataChannel ==  /\  dataWir!Next
                /\  UNCHANGED <<receiveReqQueue, sendReqQueue, requestNum, sequenceNum, windowStart, windowEnd, mess, messOut, senderState, reciverState, synNum, reqNum>>

reqChannel ==  /\  reqWir!Next
               /\  UNCHANGED <<sendDataQueue, receiveDataQueue, requestNum, sequenceNum, windowStart, windowEnd, mess, messOut, senderState, reciverState, synNum, reqNum>>

senderChannel ==   /\  sender!Next
                   /\  UNCHANGED <<receiveDataQueue, sendReqQueue, requestNum, messOut, reciverState, synNum>>

reciverChannel == /\  reciver!Next
                  /\  UNCHANGED <<sendDataQueue, receiveReqQueue, sequenceNum, windowStart, windowEnd, mess , senderState, reqNum>>
                  
------------------------------------   
\* defines the next step of the algorithim as being the next step of any one of these
Next ==  \/ dataChannel 
         \/ reqChannel
         \/ senderChannel
         \/ reciverChannel

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(dataChannel /\ Len(receiveDataQueue') = 2  /\ receiveDataQueue'[1] = requestNum)
        (* The following lines inforce the fairness properties of the modules.
           This means that for each of these modules the defined proccess within 
           that have been flaged as either strong or weak fairness will eventually 
           be run*)
        /\ sender!Fairness
        /\ reciver!Fairness
        /\ dataWir!Fairness
        /\ reqWir!Fairness
\*        (* The following line inforce the invariants of the modules. This is used 
\*           for type checking*)
\*        /\ sender!Invariants
\*        /\ reciver!Invariants
\*        /\ dataWir!Invariants
       
---------
\* This is used to check that the final output matches the orignal input
\* make sure to add "Properties" in the modules properties tab
CorrectResult == <>(messOut = MESSAGES)

Properties == /\ CorrectResult

-------------       
                  
                  
=============================================================================
\* Modification History
\* Last modified Wed Jun 12 21:14:46 NZST 2019 by sdmsi
\* Created Fri Jun 07 00:33:58 NZST 2019 by sdmsi
