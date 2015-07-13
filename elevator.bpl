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
        assume false;
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
      $Ignores[mid][_event.eCloseDoor] := false;

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
      $Ignores[mid][_event.eOpenDoor] := false;
      $Defers[mid][_event.eCloseDoor] := false;

      if (e == _event.eDoorOpened)
      {
        $State[mid] := _machine.elevator.doorOpened;
        $Defers[mid][_event.eCloseDoor] := true;
        call _machine.elevator.doorOpened.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.doorOpened)
    {
      $Defers[mid][_event.eCloseDoor] := false;

      if (e == _event.eTimerFired)
      {
        $State[mid] := _machine.elevator.doorOpenedOkToClose;
        $Defers[mid][_event.eOpenDoor] := true;
        call _machine.elevator.doorOpenedOkToClose.entry(mid);
      }
      else if (e == _event.eStopTimerReturned)
      {
        $State[mid] := _machine.elevator.doorOpened;
        $Defers[mid][_event.eCloseDoor] := true;
        call _machine.elevator.doorOpened.entry(mid);
      }
      else if (e == _event.eOpenDoor)
      {
        assert false;
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.doorOpenedOkToClose)
    {
      $Defers[mid][_event.eOpenDoor] := false;

      if (e == _event.eStopTimerReturned)
      {
        $State[mid] := _machine.elevator.doorClosing;
        $Defers[mid][_event.eCloseDoor] := true;
        call _machine.elevator.doorClosing.entry(mid);
      }
      else if (e == _event.eTimerFired)
      {
        $State[mid] := _machine.elevator.doorClosing;
        $Defers[mid][_event.eCloseDoor] := true;
        call _machine.elevator.doorClosing.entry(mid);
      }
      else if (e == _event.eCloseDoor)
      {
        assert false;
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.doorClosing)
    {
      $Defers[mid][_event.eCloseDoor] := false;

      if (e == _event.eOpenDoor)
      {
        $State[mid] := _machine.elevator.stoppingDoor;
        $Defers[mid][_event.eCloseDoor] := true;
        call _machine.elevator.stoppingDoor.entry(mid);
      }
      else if (e == _event.eDoorClosed)
      {
        $State[mid] := _machine.elevator.doorClosed;
        call _machine.elevator.doorClosed.entry(mid);
      }
      else if (e == _event.eObjectDetected)
      {
        $State[mid] := _machine.elevator.doorOpening;
        call _machine.elevator.doorOpening.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.stoppingDoor)
    {
      $Defers[mid][_event.eCloseDoor] := false;

      if (e == _event.eDoorOpened)
      {
        $State[mid] := _machine.elevator.doorOpened;
        $Defers[mid][_event.eCloseDoor] := true;
        call _machine.elevator.doorOpened.entry(mid);
      }
      else if (e == _event.eDoorClosed)
      {
        $State[mid] := _machine.elevator.doorClosed;
        call _machine.elevator.doorClosed.entry(mid);
      }
      else if (e == _event.eDoorStopped)
      {
        $State[mid] := _machine.elevator.doorOpening;
        call _machine.elevator.doorOpening.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.stoppingTimer)
    {
      $Defers[mid][_event.eOpenDoor] := false;
      $Defers[mid][_event.eCloseDoor] := false;
      $Defers[mid][_event.eObjectDetected] := false;

      if (e == _event.eOperationSuccess)
      {
        $State[mid] := _machine.elevator.returnState;
        call _machine.elevator.returnState.entry(mid);
      }
      else if (e == _event.eOperationFailure)
      {
        $State[mid] := _machine.elevator.waitingForTimer;
        $Defers[mid][_event.eOpenDoor] := true;
        $Defers[mid][_event.eCloseDoor] := true;
        $Defers[mid][_event.eObjectDetected] := true;
        call _machine.elevator.waitingForTimer.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.elevator.waitingForTimer)
    {
      $Defers[mid][_event.eOpenDoor] := false;
      $Defers[mid][_event.eCloseDoor] := false;
      $Defers[mid][_event.eObjectDetected] := false;

      if (e == _event.eTimerFired)
      {
        $State[mid] := _machine.elevator.returnState;
        call _machine.elevator.returnState.entry(mid);
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
  // var timer: int;

  $bb0:
    call door := $create_machine(_machine.door, mid);
    $Heap[mid][_machine.elevator.door] := door;
    // call timer := $create_machine(_machine.timer, mid);
    // $Heap[mid][_machine.elevator.timer] := timer;
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

procedure {:inline 1} {:entry} _machine.elevator.doorOpened.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.doorOpened.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.elevator.door], _event.eSendCommandToResetDoor, $NULL);
    // call $send($Heap[mid][_machine.elevator.timer], _event.eStartDoorCloseTimer, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.doorOpenedOkToClose.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.doorOpenedOkToClose.entry(mid: int)
{
  $bb0:
    // call $send($Heap[mid][_machine.elevator.timer], _event.eStartDoorCloseTimer, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.doorClosing.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.doorClosing.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.elevator.door], _event.eSendCommandToCloseDoor, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.stoppingDoor.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.stoppingDoor.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.elevator.door], _event.eSendCommandToStopDoor, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.stoppingTimer.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.stoppingTimer.entry(mid: int)
{
  $bb0:
    // call $send($Heap[mid][_machine.elevator.timer], _event.eStopDoorCloseTimer, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.waitingForTimer.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.waitingForTimer.entry(mid: int)
{
  $bb0:
    return;
}

procedure {:inline 1} {:entry} _machine.elevator.returnState.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.elevator.returnState.entry(mid: int)
{
  $bb0:
    call $raise(mid, _event.eStopTimerReturned, $NULL);
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
      $Ignores[mid][_event.eSendCommandToStopDoor] := false;
      $Ignores[mid][_event.eSendCommandToResetDoor] := false;
      $Ignores[mid][_event.eResetDoor] := false;

      if (e == _event.eSendCommandToOpenDoor)
      {
        $State[mid] := _machine.door.openDoor;
        call _machine.door.openDoor.entry(mid);
      }
      else if (e == _event.eSendCommandToCloseDoor)
      {
        $State[mid] := _machine.door.considerClosingDoor;
        call _machine.door.considerClosingDoor.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.door.openDoor)
    {
      if (e == _event.eUnit)
      {
        $State[mid] := _machine.door.resetDoor;
        $Ignores[mid][_event.eSendCommandToOpenDoor] := true;
        $Ignores[mid][_event.eSendCommandToCloseDoor] := true;
        $Ignores[mid][_event.eSendCommandToStopDoor] := true;
        call _machine.door.resetDoor.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.door.considerClosingDoor)
    {
      if (e == _event.eUnit)
      {
        $State[mid] := _machine.door.closeDoor;
        call _machine.door.closeDoor.entry(mid);
      }
      else if (e == _event.eObjectEncountered)
      {
        $State[mid] := _machine.door.objectEncountered;
        call _machine.door.objectEncountered.entry(mid);
      }
      else if (e == _event.eSendCommandToStopDoor)
      {
        $State[mid] := _machine.door.stopDoor;
        call _machine.door.stopDoor.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.door.objectEncountered)
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
    else if ($State[mid] == _machine.door.closeDoor)
    {
      if (e == _event.eUnit)
      {
        $State[mid] := _machine.door.resetDoor;
        $Ignores[mid][_event.eSendCommandToOpenDoor] := true;
        $Ignores[mid][_event.eSendCommandToCloseDoor] := true;
        $Ignores[mid][_event.eSendCommandToStopDoor] := true;
        call _machine.door.resetDoor.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.door.stopDoor)
    {
      if (e == _event.eUnit)
      {
        $State[mid] := _machine.door.openDoor;
        call _machine.door.openDoor.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.door.resetDoor)
    {
      $Ignores[mid][_event.eSendCommandToOpenDoor] := false;
      $Ignores[mid][_event.eSendCommandToCloseDoor] := false;
      $Ignores[mid][_event.eSendCommandToStopDoor] := false;

      if (e == _event.eSendCommandToResetDoor)
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
    call $send($Heap[mid][_machine.door.elevator], _event.eDoorOpened, $NULL);
    call $raise(mid, _event.eUnit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.door.considerClosingDoor.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door.considerClosingDoor.entry(mid: int)
{
  $bb0:
    if (*)
    {
      call $raise(mid, _event.eUnit, $NULL);
    }
    else if (*)
    {
      call $raise(mid, _event.eObjectEncountered, $NULL);
    }
    return;
}

procedure {:inline 1} {:entry} _machine.door.objectEncountered.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door.objectEncountered.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.door.elevator], _event.eObjectDetected, $NULL);
    call $raise(mid, _event.eUnit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.door.closeDoor.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door.closeDoor.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.door.elevator], _event.eDoorClosed, $NULL);
    call $raise(mid, _event.eUnit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.door.stopDoor.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door.stopDoor.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.door.elevator], _event.eDoorStopped, $NULL);
    call $raise(mid, _event.eUnit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.door.resetDoor.entry(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.door.resetDoor.entry(mid: int)
{
  $bb0:
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
