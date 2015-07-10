// Program
var $CurrMid: int;
var $Inbox: [int][int]Event;
var $InboxSize: [int]int;
var $Payload: [int]Payload;

var {:thread_local} $Heap: [int][int]int;
var {:thread_local} $State: [int]State;
var {:thread_local} $IsHalted: [int]bool;
var {:thread_local} $Raised: [int]Event;
var {:thread_local} $Ignores: [int][Event]bool;
var {:thread_local} $Defers: [int][Event]bool;


// Types
type Machine;
type State;
type Event;
type Payload = int;

const unique $DEFAULT: Event;
const unique $HALT: Event;

const unique $NULL: int;
axiom $NULL == 0;


// Machinery
procedure {:inline 1} $create_machine(m: Machine, p: Payload) returns (r: int);
  modifies $CurrMid, $Heap, $State, $IsHalted, $InboxSize, $Payload;

implementation {:inline 1} $create_machine(m: Machine, p: Payload) returns (mid: int)
{
  $bb0:
    mid := $CurrMid;
    $CurrMid := $CurrMid + 1;

    $InboxSize[mid] := 0;
    $Payload[mid] := p;

    if (m == _machine.user)
    {
      async call _machine.user.constructor(mid);
    }
    else if (m == _machine.elevator)
    {
      async call _machine.elevator.constructor(mid);
    }
    else if (m == _machine.door)
    {
      async call _machine.door.constructor(mid);
    }

    return;
}

procedure {:inline 1} $raise(mid: int, e: Event, p: Payload);
  modifies $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} $raise(mid: int, e: Event, p: Payload)
{
  $bb0:
    $Payload[mid] := p;
    $Raised[mid] := e;
    return;
}

procedure {:inline 1} $send(mid: int, e: Event, p: Payload);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} $send(mid: int, e: Event, p: Payload)
{
  var index: int;

  $bb0:
    index := $InboxSize[mid];
    $Inbox[mid][index] := e;
    $InboxSize[mid] := $InboxSize[mid] + 1;
    $Payload[mid] := p;
    return;
}

procedure {:inline 1} $q_remove(mid: int, idx: int);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} $q_remove(mid: int, idx: int)
{
  var index: int;

  $bb0:
    index := idx;

    while (index < $InboxSize[mid] - 1)
    {
      $Inbox[mid][index] := $Inbox[mid][index + 1];
      index := index + 1;
    }

    $InboxSize[mid] := $InboxSize[mid] - 1;

    return;
}

procedure {:inline 1} $run_event_handler(mid: int, mtype: Machine);
  modifies $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} $run_event_handler(mid: int, mtype: Machine)
{
  var nextEvent: Event;

  $bb0:
    nextEvent := $DEFAULT;
    while (!$IsHalted[mid])
    {
      call nextEvent := $get_next_event(mid);
      if (nextEvent == $DEFAULT)
      {
        break;
      }
      else if (nextEvent == $HALT)
      {
        $IsHalted[mid] := true;
        break;
      }

      if (mtype == _machine.user)
      {
        call _machine.user.handle_event(mid, nextEvent);
      }
      else if (mtype == _machine.elevator)
      {
        call _machine.elevator.handle_event(mid, nextEvent);
      }
      else if (mtype == _machine.door)
      {
        call _machine.door.handle_event(mid, nextEvent);
      }
    }

    return;
}

procedure {:inline 1} $get_next_event(mid: int) returns (r: Event);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} $get_next_event(mid: int) returns (r: Event)
{
  var nextEvent: Event;
  var index: int;
  var inbox: [int] Event;
  var size: int;

  $bb0:
    nextEvent := $DEFAULT;

    index := 0;
    if ($Raised[mid] != $DEFAULT)
    {
      nextEvent := $Raised[mid];
      $Raised[mid] := $DEFAULT;
    }
    else
    {
      yield;
      while (index < $InboxSize[mid])
      {
        if ($Ignores[mid][$Inbox[mid][index]])
        {
          call $q_remove(mid, index);
          index := index - 1;
        }
        else if (!$Defers[mid][$Inbox[mid][index]])
        {
          nextEvent := $Inbox[mid][index];
          call $q_remove(mid, index);
          break;
        }

        index := index + 1;
      }
    }

    r := nextEvent;
    return;
}


// Events
const unique _event.eOpenDoor: Event;
const unique _event.eCloseDoor: Event;
const unique _event.eResetDoor: Event;
const unique _event.eDoorOpened: Event;
const unique _event.eDoorClosed: Event;
const unique _event.eDoorStopped: Event;
const unique _event.eObjectDetected: Event;
const unique _event.eTimerFired: Event;
const unique _event.eOperationSuccess: Event;
const unique _event.eOperationFailure: Event;
const unique _event.eSendCommandToOpenDoor: Event;
const unique _event.eSendCommandToCloseDoor: Event;
const unique _event.eSendCommandToStopDoor: Event;
const unique _event.eSendCommandToResetDoor: Event;
const unique _event.eStartDoorCloseTimer: Event;
const unique _event.eStopDoorCloseTimer: Event;
const unique _event.eUnit: Event;
const unique _event.eStopTimerReturned: Event;
const unique _event.eObjectEncountered: Event;


// Machine: user
const {:main} unique _machine.user: Machine;
const {:start} unique _machine.user.init: State;
const unique _machine.user.loop: State;

const unique _machine.user.elevator: int;

procedure {:inline 1} _machine.user.constructor(mid: int);
  modifies $Heap, $State, $IsHalted, $InboxSize;

implementation {:inline 1} _machine.user.constructor(mid: int)
{
  $bb0:
    $IsHalted[mid] := false;
    $State[mid] := _machine.user.init;
    $Heap[mid][_machine.user.elevator] := $NULL;

    assume (forall e:Event :: $Ignores[mid][e] == false);
    assume (forall e:Event :: $Defers[mid][e] == false);

    call _machine.user.init.entry(mid);
    call $run_event_handler(mid, _machine.user);
    return;
}

procedure {:inline 1} _machine.user.handle_event(mid: int, e: Event);
  modifies $State, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} _machine.user.handle_event(mid: int, e: Event)
{
  $bb0:
    if ($State[mid] == _machine.user.init)
    {
      if (e == _event.eUnit)
      {
        $State[mid] := _machine.user.loop;
        call _machine.user.loop.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.user.loop)
    {
      if (e == _event.eUnit)
      {
        call _machine.user.loop.entry(mid);
      }
      else
      {
        assert false;
      }
    }

    return;
}

procedure {:inline 1} {:entry} _machine.user.init.entry(mid: int);
  modifies $CurrMid, $IsHalted, $Heap, $State, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.user.init.entry(mid: int)
{
  var elevator: int;

  $bb0:
    call elevator := $create_machine(_machine.elevator, $NULL);
    $Heap[mid][_machine.user.elevator] := elevator;
    call $raise(mid, _event.eUnit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.user.loop.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.user.loop.entry(mid: int)
{
  $bb0:
    if (*)
    {
      call $send($Heap[mid][_machine.user.elevator], _event.eOpenDoor, $NULL);
    }
    else if (*)
    {
      call $send($Heap[mid][_machine.user.elevator], _event.eCloseDoor, $NULL);
    }

    // call $raise(mid, _event.eUnit, $NULL);
    return;
}


// Machine: elevator
const {:main} unique _machine.elevator: Machine;
const {:start} unique _machine.elevator.init: State;
const unique _machine.elevator.doorClosed: State;
const unique _machine.elevator.doorOpening: State;
const unique _machine.elevator.doorOpened: State;
const unique _machine.elevator.doorOpenedOkToClose: State;
const unique _machine.elevator.doorClosing: State;
const unique _machine.elevator.stoppingDoor: State;
const unique _machine.elevator.stoppingTimer: State;
const unique _machine.elevator.waitingForTimer: State;
const unique _machine.elevator.returnState: State;

const unique _machine.elevator.door: int;

procedure {:inline 1} _machine.elevator.constructor(mid: int);
  modifies $Heap, $State, $IsHalted, $InboxSize;

implementation {:inline 1} _machine.elevator.constructor(mid: int)
{
  $bb0:
    $IsHalted[mid] := false;
    $State[mid] := _machine.elevator.init;
    $Heap[mid][_machine.elevator.door] := $NULL;

    assume (forall e:Event :: $Ignores[mid][e] == false);
    assume (forall e:Event :: $Defers[mid][e] == false);

    call _machine.elevator.init.entry(mid);
    call $run_event_handler(mid, _machine.elevator);
    return;
}

procedure {:inline 1} _machine.elevator.handle_event(mid: int, e: Event);
  modifies $State, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} _machine.elevator.handle_event(mid: int, e: Event)
{
  $bb0:
    if ($State[mid] == _machine.elevator.init)
    {
      if (e == _event.eUnit)
      {
        $State[mid] := _machine.elevator.doorClosed;
        $Ignores[mid][_event.eCloseDoor] := true;
        call _machine.elevator.doorClosed.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.doorClosed)
    {
      if (e == _event.eOpenDoor)
      {
        $State[mid] := _machine.elevator.doorOpening;
        $Ignores[mid][_event.eOpenDoor] := true;
        $Defers[mid][_event.eCloseDoor] := true;
        call _machine.elevator.doorOpening.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.doorOpening)
    {
      if (e == _event.eOpenDoor)
      {
        // call _machine.elevator.doorOpening.entry(mid);
      }
      else
      {
        assert false;
      }
    }

    return;
}

procedure {:inline 1} {:entry} _machine.elevator.init.entry(mid: int);
  modifies $CurrMid, $IsHalted, $Heap, $State, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.init.entry(mid: int)
{
  var door: int;

  $bb0:
    call door := $create_machine(_machine.door, mid);
    $Heap[mid][_machine.elevator.door] := door;
    call $raise(mid, _event.eUnit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.doorClosed.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.doorClosed.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.elevator.door], _event.eSendCommandToResetDoor, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.doorOpening.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.doorOpening.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.elevator.door], _event.eSendCommandToOpenDoor, $NULL);
    return;
}


// Machine: door
const {:main} unique _machine.door: Machine;
const {:start} unique _machine.door._init: State;
const unique _machine.door.init: State;
const unique _machine.door.openDoor: State;
const unique _machine.door.considerClosingDoor: State;
const unique _machine.door.objectEncountered: State;
const unique _machine.door.closeDoor: State;
const unique _machine.door.stopDoor: State;
const unique _machine.door.resetDoor: State;

const unique _machine.door.elevator: int;

procedure {:inline 1} _machine.door.constructor(mid: int);
  modifies $Heap, $State, $IsHalted, $InboxSize;

implementation {:inline 1} _machine.door.constructor(mid: int)
{
  $bb0:
    $IsHalted[mid] := false;
    $State[mid] := _machine.door._init;
    $Heap[mid][_machine.door.elevator] := $NULL;

    assume (forall e:Event :: $Ignores[mid][e] == false);
    assume (forall e:Event :: $Defers[mid][e] == false);

    call _machine.door._init.entry(mid);
    call $run_event_handler(mid, _machine.door);
    return;
}

procedure {:inline 1} _machine.door.handle_event(mid: int, e: Event);
  modifies $State, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} _machine.door.handle_event(mid: int, e: Event)
{
  $bb0:
    if ($State[mid] == _machine.door._init)
    {
      if (e == _event.eUnit)
      {
        $State[mid] := _machine.door.init;
        $Ignores[mid][_event.eSendCommandToStopDoor] := true;
        $Ignores[mid][_event.eSendCommandToResetDoor] := true;
        $Ignores[mid][_event.eResetDoor] := true;
        call _machine.door.init.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.door.init)
    {
      if (e == _event.eSendCommandToOpenDoor)
      {
        $State[mid] := _machine.door.openDoor;
        call _machine.door.openDoor.entry(mid);
      }
      else if (e == _event.eSendCommandToCloseDoor)
      {
        // call _machine.door.loop.entry(mid);
      }
      else
      {
        assert false;
      }
    }

    return;
}

procedure {:inline 1} {:entry} _machine.door._init.entry(mid: int);
  modifies $CurrMid, $IsHalted, $Heap, $State, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door._init.entry(mid: int)
{
  $bb0:
    $Heap[mid][_machine.door.elevator] := $Payload[mid];
    call $raise(mid, _event.eUnit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.door.init.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door.init.entry(mid: int)
{
  $bb0:
    return;
}

procedure {:inline 1} {:entry} _machine.door.openDoor.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door.openDoor.entry(mid: int)
{
  $bb0:
    assert false;
    return;
}


// Entry point
procedure {:entrypoint} Main();
  modifies $CurrMid, $Heap, $State, $IsHalted, $InboxSize, $Payload;

implementation {:entrypoint} Main()
{
  var m: int;

  $main:
    assume $CurrMid > 0;
    call m := $create_machine(_machine.user, $NULL);
    return;
}
