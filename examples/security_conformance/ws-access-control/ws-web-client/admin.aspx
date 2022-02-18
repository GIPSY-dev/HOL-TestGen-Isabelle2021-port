<%@ Page Language="C#" validateRequest="false" MaintainScrollPositionOnPostBack="true" %>
<script runat="server">      
  String User;
  String Role;

  protected void Page_Init(Object s, EventArgs e) { 
    User = Request.QueryString["user"];
    Role = logic.getRole(User);
  }

  protected void createSCR(Object s, EventArgs e) { 
    logic.createSCR(User, Role, logic.patientToID(csScrID.Text), csResult);
  }

  protected void deleteSCR(Object s, EventArgs e) { 
    logic.deleteSCR(User, Role, logic.patientToID(dsScrID.Text), dsResult);
  }

  protected void addLR(Object s, EventArgs e) { 
    logic.addLR(User, Role,
                Convert.ToInt32(alLrID.Text),
                logic.patientToID(alLrScrID.Text),
                logic.parseUsers(alLrUsers.Text),
                alResult);
  }

  protected void removeLR(Object s, EventArgs e) { 
    logic.removeLR(User, Role, Convert.ToInt32(rlLrID.Text), rlResult);
  }
</script><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
  <title>Healthcare - <%= User %></title>
  <link rel="stylesheet" href="<%= logic.getStyle(User) %>" type="text/css" />
  <link rel="stylesheet" href="styles.css" type="text/css" />
</head>
<body>
<div id="wrap">
  <div id="header">
    <div id="header-text">
      <h1><a href="#">Health<span>care</span></a></h1>
      <h2><%= Role %></h2>
    </div>
  </div>

  <div id="navigation">
    <ul>
      <li><a href="read.aspx?user=<%= User %>">read</a></li>
      <li><a href="modify.aspx?user=<%= User %>">modify</a></li>
      <li class="selected"><a href="#">add/delete</a></li>
    </ul>
  </div>

  <div id="content">
    <div id="page">
      <form id="form" method="post" runat="server">
        <asp:Panel defaultbutton="cs" runat="server">
        <fieldset>
          <legend>Create Summary Care Record</legend>
          <div><label for="csScrID">Patient</label>
          <asp:TextBox id="csScrID" runat="server" /></div>
          <asp:Button id="cs" OnClick="createSCR" runat="server" class="formbutton" Text="Create" />
          <span id="csResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>

        <asp:Panel defaultbutton="ds" runat="server">
        <fieldset>
          <legend>Delete Summary Care Record</legend>
          <div><label for="dsScrID">Patient</label>
          <asp:TextBox id="dsScrID" runat="server" /></div>
          <asp:Button id="ds" OnClick="deleteSCR" runat="server" class="formbutton" Text="Delete" />
          <span id="dsResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>

        <asp:Panel defaultbutton="al" runat="server">
        <fieldset>
          <legend>Add Legitimate Relationship</legend>
          <div><label for="alLrID">Legitimate Relationship ID</label>
          <asp:TextBox id="alLrID" runat="server" /></div>

          <div><label for="alLrScrID">Patient</label>
          <asp:TextBox id="alLrScrID" runat="server" /></div>

          <div><label for="alLrUsers">Users</label>
          <asp:TextBox id="alLrUsers" runat="server" /></div>
          <asp:Button id="al" OnClick="addLR" runat="server" class="formbutton" Text="Add" />
          <span id="alResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>

        <asp:Panel defaultbutton="rl" runat="server">
        <fieldset>
          <legend>Remove Legitimate Relationship</legend>
          <div><label for="rlLrID">Legitimate Relationship ID</label>
          <asp:TextBox id="rlLrID" runat="server" /></div>
          <asp:Button id="rl" OnClick="removeLR" runat="server" class="formbutton" Text="Remove" />
          <span id="rlResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>
      </form>
    </div>
    <div class="footer">
      <p>Original design by <a href="http://www.spyka.net">spyka webmaster</a>
    | <a href="http://www.justfreetemplates.com">Free Web Templates</a>
    | <a href="http://validator.w3.org/check/referer" title="valid XHTML">XHTML</a>
    | <a href="http://jigsaw.w3.org/css-validator/check/referer" title="valid CSS">CSS</a></p>
    </div>
  </div>
</div>
</body>
</html>
