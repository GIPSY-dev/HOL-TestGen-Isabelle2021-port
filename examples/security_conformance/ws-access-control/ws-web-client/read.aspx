<%@ Page Language="C#" validateRequest="false" MaintainScrollPositionOnPostBack="true" %>
<script runat="server">      
  String User;
  String Role;

  protected void Page_Init(Object s, EventArgs e) { 
    User = Request.QueryString["user"];
    Role = logic.getRole(User);
  }

  protected void readSCR(Object s, EventArgs e) { 
    logic.readSCR(User, Role, logic.patientToID(rsScrID.Text),
                  rsResult);
  }

  protected void readEntry(Object s, EventArgs e) { 
    logic.readEntry(User, Role, logic.patientToID(reScrID.Text),
                    reEntryID.Text,
                    reResult);
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
      <li class="selected"><a href="#">read</a></li>
      <li><a href="modify.aspx?user=<%= User %>">modify</a></li>
      <li><a href="admin.aspx?user=<%= User %>">add/delete</a></li>
    </ul>
  </div>

  <div id="content">
    <div id="page">
      <form id="form" method="post" runat="server">
        <asp:Panel defaultbutton="rs" runat="server">
        <fieldset>
          <legend>Read Summary Care Record</legend>
          <div><label for="rsScrID">Patient</label>
          <asp:TextBox id="rsScrID" runat="server" /></div>
          <asp:Button id="rs" OnClick="readSCR" runat="server" class="formbutton" Text="Read" />
          <span id="rsResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>

        <asp:Panel defaultbutton="re" runat="server">
        <fieldset>
          <legend>Read Entry</legend>
          <div><label for="reScrID">Patient</label>
          <asp:TextBox id="reScrID" runat="server" /></div>
          <div><label for="reEntryID">Entry ID</label>
          <asp:TextBox id="reEntryID" runat="server" /></div>
          <asp:Button id="re" OnClick="readEntry" runat="server" class="formbutton" Text="Read" />
          <span id="reResult" class="hidden" runat="server">Not done</span>
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
