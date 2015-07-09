class Global
{
  var machines: set<int>

  static method Foo()
  {
    machines := machines + { 1 };
  }
}

class Program
{
  //var p_machine: Machine;
  var test: bool;

  constructor()
    modifies this
  {
  //  p_machine := new Machine;
    test := false;
  //  this.Init_p_entry();
  }

  method Init_p_entry()
  //  requires this.p_machine != null
  //  modifies this.p_machine
  {
    print "entry\n";
  //  var e := new Event;
  //  e.name := "E1";
  //  p_machine.p_send(p_machine, e);
  }

  //method Action1()
  //  modifies this
  //{
  //  test := true;
  //}

  //method Action2()
  //{
  //  assert test == false;
  //}
}

class Machine<T>
{
  var p_machine: T;
  var p_inbox: seq<Event>;

  constructor(m: T)
    modifies this
  {
    p_machine := m;
    p_machine.Init_p_entry();
  }

  method p_send(m: Machine, e: Event)
    requires m != null
    requires e != null
    modifies m
  {
    print "sending\n";
    m.p_enqueue(e);
  }

  method p_raise(e: Event, payload: object)
    requires e != null
  {
    print "raising\n";
  }

  method p_enqueue(e: Event)
    requires e != null
    modifies this
  {
    print "enqueing\n";
    p_inbox := [e] + p_inbox;
    var nextEvent := p_inbox[0];
    p_inbox := p_inbox[1..];
  }
}

class Event
{
  var name: string;
  var payload: object;
}

method Main()
{
  var program := new Program();
  var m := new Machine<Program>(program);
}
