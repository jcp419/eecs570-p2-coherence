
-- two-state 4-hop VI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC_Req: 0;
  VC_Fwd: 1;
  VC_Res: 2;
  QMax: 2;
  NumVCs: 3;
  NetMax: ProcCount+1;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;

  MessageType: enum {  -- received by home node
                       GetS,
                       GetM,
                       PutS,
                       PutM,
                       -- received by processor
                       Fwd_GetS,
                       Fwd_GetM,
                       Inv,
                       Put_Ack,
                       Inv_Ack,
                       -- received by both
                       Data
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      vc: VCType;
      val: Value;
      ackCount: 0..ProcCount;
      fwdDst: Node;
    End;

  HomeState:
    Record
      state: enum { H_S, H_M, H_I, 					--stable states
      							H_S_D }; 								--transient states during recall
      owner: Node;	
      sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { P_I, P_IS_D, P_IM_AD, P_IM_A, P_II_A
                    P_S, P_SM_AD, P_SM_A, P_SI_A
                    P_M, P_MI_A
                  };
      val: Value;
      ackCount: 0..ProcCount;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
  InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
         vc:VCType;
         val:Value;
         ackCount:0..ProcCount; -- number of inv-acks we need to receive -- only used when sharing data to new owner
         fwdDst:Node; -- where to send a response when dealing with forwarding, acks
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype    := mtype;
  msg.src      := src;
  msg.vc       := vc;
  msg.val      := val;
  msg.ackCount := ackCount;
  msg.fwdDst  := fwdDst;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

-- These aren't needed for Valid/Invalid protocol, but this is a good way of writing these functions
Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Procedure RemoveAllSharers();
Begin
  MultiSetRemovePred(i:HomeNode.sharers, true); -- better way to do this? lol
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send invalidation message here 
        Send(Inv, n, HomeType, VC_Fwd, UNDEFINED, 0, rqst); -- sharer should send inv-ack to rqst
      endif;
    endif;
  endfor;
End;


Procedure HomeReceive(msg:Message);
var numSharers:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we put this inside a switch, so it is useful to
  -- pre-calculate the sharer count here
  numSharers := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case H_I:
    switch msg.mtype
    case GetS:
      -- send data to req
      Send(Data, msg.src, HomeType, VC_Res, HomeNode.val, 0, UNDEFINED);
      -- add req to sharers
      AddToSharersList(msg.src);

      HomeNode.state := H_S;
    case GetM:
      -- send data to req
      Send(Data, msg.src, HomeType, VC_Res, HomeNode.val, 0, UNDEFINED);
      -- set owner to req
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;
    case PutS:
      -- send put_ack to req
      Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
    case PutM:
      -- send put_ack to req
      Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_S:
    switch msg.mtype
    case GetS:
      -- send data to req
      Send(Data, msg.src, HomeType, VC_Res, HomeNode.val, 0, UNDEFINED);
      -- add req to sharers
      AddToSharersList(msg.src);
    case GetM:
      -- send data to Req,
      if (IsSharer(msg.src)) then
        -- node is trying to upgrade from S to M
        -- ackCount = numSharers - 1, since proc doesn't expect ack from itself
        Send(Data, msg.src, HomeType, VC_Res, HomeNode.val, numSharers - 1, UNDEFINED);
      else
        -- ackCount = numSharers
        Send(Data, msg.src, HomeType, VC_Res, HomeNode.val, numSharers, UNDEFINED);
      endif;
      -- send Inv to  all Sharers, except requester
      SendInvReqToSharers(msg.src);
      -- clear Sharers
      RemoveAllSharers();
      -- set Owner to Req/M
      HomeNode.owner := msg.src;
      HomeNode.state := H_M;
    case PutS:
      Assert(IsSharer(msg.src)); -- TODO good?
      RemoveFromSharersList(msg.src);
      Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);

      if (MultiSetCount(i:HomeNode.sharers, true) = 0) then -- TODO: checks if size is 0?
        -- we have removed the last sharer, so invalidate
        HomeNode.state := H_I;
      endif;
    case PutM:
      -- remove req from sharers
      Assert(IsSharer(msg.src)); -- TODO good? probably not?
      RemoveFromSharersList(msg.src);
      -- send put_ack to req
      Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);

      if (MultiSetCount(i:HomeNode.sharers, true) = 0) then -- TODO: checks if size is 0?
        -- we have removed the last sharer, so invalidate
        HomeNode.state := H_I;
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
  case H_M:
    switch msg.mtype
    case GetS:
      -- send fwd_getS to owner
      Send(Fwd_GetS, HomeNode.owner, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
      -- add req and owner to sharers
      AddToSharersList(HomeNode.owner);
      AddToSharersList(msg.src);
      -- clear owner
      undefine HomeNode.owner;
      -- state goes to H_S_D
      HomeNode.state := H_S_D;
    case GetM:
      -- send fwd_getm to owner
      Send(Fwd_GetM, HomeNode.owner, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
      -- set owner to req
      HomeNode.owner := msg.src;
    case PutS:
      -- send put_ack to req
      Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
    case PutM:
      if (msg.src = HomeNode.owner) then
        -- src is owner
        -- copy data to memory
        HomeNode.val := msg.val;
        -- clear owner
        undefine HomeNode.owner;
        -- send put_ack to req
        Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
        HomeNode.state := H_I;
      else
        -- src is non-owner
        -- send put_ack to req
        Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
  case H_S_D:
    switch msg.mtype
    case GetS:
      -- stall
      msg_processed := false;
    case GetM:
      -- stall
      msg_processed := false;
    case PutS:
      Assert(IsSharer(msg.src)); -- TODO good?
      -- remove req from sharers
      RemoveFromSharersList(msg.src);
      -- send put_ack to req
      Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);
    case PutM:
      -- remove req from sharers
      Assert(IsSharer(msg.src)); -- TODO good? probably not?
      RemoveFromSharersList(msg.src);
      -- send put_ack to req
      Send(Put_Ack, msg.src, HomeType, VC_Fwd, UNDEFINED, UNDEFINED, UNDEFINED);

      if (MultiSetCount(i:HomeNode.sharers, true) = 0) then -- TODO: checks if size is 0?
        -- we have removed the last sharer, so invalidate
        HomeNode.state := H_I;
      endif;
    case Data:
      -- copy data to memory
      HomeNode.val := msg.val;
      HomeNode.state := H_S;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
  endswitch;
End;


Procedure ProcReceive(msg:Message; p:Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  alias pAckCount:Procs[p].ackCount do

  switch ps
  -- case P_I: NO MESSAGES POSSIBLE 
  case P_IS_D:
    switch msg.mtype
    case Inv:
      -- stall
      msg_processed := false;
    case Data:
      Assert(msg.src = HomeNode.owner | pAckCount = 0); -- TODO ?
      pv = msg.val;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  case P_IM_AD: 
    switch msg.mtype
    case Fwd_GetS:
      msg_processed := false;
    case Fwd_GetM:
      msg_processed := false;
    case Data:
      pv := msg.val;
      if (msg.src = HomeNode.owner) then
        ps := P_M;
      elsif (pAckCount = 0) then
        ps := P_M;
      else
        ps := P_IM_A;
      endif;
    case Inv_Ack:
      pAckCount := pAckCount - 1;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  case P_IM_A: 
    switch msg.mtype
    case Fwd_GetS:
      msg_processed := false;
    case Fwd_GetM:
      msg_processed := false;
    case Inv_Ack:
      if (pAckCount = 0) then
        ps := P_M;
      else
        pAckCount := pAckCount - 1;
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endif; 
  case P_II_A: 
    switch msg.mtype
    case Put_Ack:
      ps := P_I;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endif; 
  case P_S: 
    switch msg.mtype
    case Inv:
      -- send inv_ack to req
      Send(Inv_Ack, msg.fwdDst, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      undefine pv;
      ps := P_I;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  case P_SM_AD: 
    switch msg.mtype
    case Fwd_GetS:
      msg_processed := false;
    case Fwd_GetM:
      msg_processed := false;
    case Inv:
      Send(Inv_Ack, msg.fwdDst, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := P_IM_AD;
    case Data:
      pv := msg.val;
      if (msg.src = HomeNode.owner) then
        ps := P_M;
      elsif (pAckCount = 0) then
        ps := P_M;
      else
        ps := P_SM_A;
      endif;
    case Inv_Ack:
      pAckCount := pAckCount - 1;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  case P_SM_A: 
    switch msg.mtype
    case Fwd_GetS:
      msg_processed := false;
    case Fwd_GetM:
      msg_processed := false; 
    case Inv_Ack:
      if (pAckCount = 0) then
        ps := P_M;
      else
        pAckCount := pAckCount - 1;
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  case P_SI_A:  
    switch msg.mtype
    case Inv:
      -- send inv_ack to req
      Send(Inv_Ack, msg.fwdDst, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := P_II_A
    case Put_Ack:
      ps := P_I;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endif;
  case P_M: 
    switch msg.mtype
    case Fwd_GetS:
      -- send data to req
      Send(Data, msg.fwdDst, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      -- send data to dir
      Send(Data, HomeType, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := P_S;
    case Fwd_GetM:
      -- send data to req
      Send(Data, msg.fwdDst, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := P_I;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  case P_MI_A:
    switch msg.mtype
    case Fwd_GetS:
      -- send data to req
      Send(Data, msg.fwdDst, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      -- send data to dir
      Send(Data, HomeType, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := P_SI_A;
    case Fwd_GetM:
      -- send data to req
      Send(Data, msg.fwdDst, p, VC_Res, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := P_II_A;
    case Put_Ack:
      ps := P_I;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
  
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do

	ruleset v:Value Do
  	rule "store new value"
   	 (p.state = P_Valid)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
  	endrule;
	endruleset;

  rule "read request"
    p.state = P_Invalid 
  ==>
    Send(ReadReq, HomeType, n, VC0, UNDEFINED);
    p.state := PT_Pending;
  endrule;


  rule "writeback"
    (p.state = P_Valid)
  ==>
    Send(WBReq, HomeType, n, VC1, p.val); 
    p.state := PT_WritebackPending;
    undefine p.val;
  endrule;

  endalias;
endruleset;

-- Message delivery rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
    rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
			endif;

			if msg_processed
			then
				-- Message has been handled, forget it
	  		undefine InBox[n][vc];
			endif;
	  
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := H_I;
  undefine HomeNode.owner;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_Invalid;
    undefine Procs[i].val;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = H_I
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = H_I 
    ->
			HomeNode.val = LastWrite;

invariant "values in valid state match last write"
  Forall n : Proc Do	
     Procs[n].state = P_Valid
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_Invalid
    ->
			IsUndefined(Procs[n].val)
	end;
	
	
-- Here are some invariants that are helpful for validating shared state.

invariant "modified implies empty sharers list"
  HomeNode.state = H_Modified
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_I
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     HomeNode.state = H_Shared | HomeNode.state = H_I
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_Shared & Procs[n].state = P_Shared
    ->
			HomeNode.val = Procs[n].val
	end;