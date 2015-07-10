class Event
{
  var name: string;
  var payload: object;
}

trait Machine
{
  var p_inbox: seq<Event>;

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

class Server extends Machine
{
  var client: Machine;

  constructor()
    modifies this
  {
    this.client := null;
    this.Init_p_entry();
  }

  method Init_p_entry()
    modifies this
  {
    print "server entry\n";
    this.client := new Client();
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

class Client extends Machine
{
  var server: Machine;

  constructor()
    modifies this
  {
    server := null;
    this.Init_p_entry();
  }

  method Init_p_entry()
  {
    print "client entry\n";
  }
}

method Main()
{
  var m := new Server();
}
