<%@ Page Language="C#" validateRequest="false" MaintainScrollPositionOnPostBack="true" %>
<script runat="server">      
  String User;
  String Role;

  protected void Page_Init(Object s, EventArgs e) { 
    User = Request.QueryString["user"];
    Role = logic.getRole(User);
  }

  protected void appendEntry(Object s, EventArgs e) { 
    logic.appendEntry(User, Role, logic.patientToID(aeScrID.Text),
                      aeEntryID.Text, aeData.Text, aeEntryStatus.Text,
                      aeResult);
  }

  protected void deleteEntry(Object s, EventArgs e) { 
    logic.deleteEntry(User, Role, logic.patientToID(deScrID.Text),
                      deEntryID.Text,
                      deResult);
  }

  protected void changeStatus(Object s, EventArgs e) { 
    logic.changeStatus(User, Role, logic.patientToID(ceScrID.Text),
                       ceEntryID.Text,
                       ceEntryStatus.Text,
                       ceResult);
  }

  protected void editEntry(Object s, EventArgs e) { 
    logic.editEntry(User, Role, logic.patientToID(eeScrID.Text),
                    eeEntryID.Text,
                    eeData.Text,
                    eeResult);
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
      <li class="selected"><a href="modify.aspx?user=<%= User %>">modify</a></li>
      <li><a href="admin.aspx?user=<%= User %>">add/delete</a></li>
    </ul>
  </div>

  <div id="content">
    <div id="page">
      <form id="form" method="post" runat="server">
        <asp:Panel defaultbutton="ae" runat="server">
        <fieldset>
          <legend>Append Entry</legend>
          <div><label for="aeScrID">Patient</label>
          <asp:TextBox id="aeScrID" runat="server" /></div>
          <div><label for="aeEntryID">Entry ID</label>
          <asp:TextBox id="aeEntryID" runat="server" /></div>
          <div><label for="aeData">Entry data</label>
          <asp:TextBox id="aeData" runat="server" /></div>
          <div class="radio"><span class="label">Entry Status</span>
            <asp:RadioButtonList id="aeEntryStatus" RepeatLayout="Flow" RepeatDirection="Horizontal" runat="server">
               <asp:ListItem selected="true">Open</asp:ListItem>
               <asp:ListItem>Closed</asp:ListItem>
            </asp:RadioButtonList>
          </div>
          <asp:Button id="ae" OnClick="appendEntry" runat="server" class="formbutton" Text="Add" />
          <span id="aeResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>

        <asp:Panel defaultbutton="de" runat="server">
        <fieldset>
          <legend>Delete Entry</legend>
          <div><label for="deScrID">Patient</label>
          <asp:TextBox id="deScrID" runat="server" /></div>
          <div><label for="deEntryID">Entry ID</label>
          <asp:TextBox id="deEntryID" runat="server" /></div>
          <asp:Button id="de" OnClick="deleteEntry" runat="server" class="formbutton" Text="Delete" />
          <span id="deResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>

        <asp:Panel defaultbutton="ce" runat="server">
        <fieldset>
          <legend>Change Entry Status</legend>
          <div><label for="ceScrID">Patient</label>
          <asp:TextBox id="ceScrID" runat="server" /></div>
          <div><label for="ceEntryID">Entry ID</label>
          <asp:TextBox id="ceEntryID" runat="server" /></div>
          <div class="radio"><span class="label">Entry Status</span>
            <asp:RadioButtonList id="ceEntryStatus" RepeatLayout="Flow" RepeatDirection="Horizontal" runat="server">
               <asp:ListItem selected="true">Open</asp:ListItem>
               <asp:ListItem>Closed</asp:ListItem>
            </asp:RadioButtonList>
          </div>
          <asp:Button id="ce" OnClick="changeStatus" runat="server" class="formbutton" Text="Change" />
          <span id="ceResult" class="hidden" runat="server">Not done</span>
        </fieldset>
        </asp:Panel>

        <asp:Panel defaultbutton="ee" runat="server">
        <fieldset>
          <legend>Edit Entry</legend>
          <div><label for="eeScrID">Patient</label>
          <asp:TextBox id="eeScrID" runat="server" /></div>
          <div><label for="eeEntryID">Entry ID</label>
          <asp:TextBox id="eeEntryID" runat="server" /></div>
          <div><label for="eeData">Entry data</label>
          <asp:TextBox id="eeData" runat="server" /></div>
          <asp:Button id="ee" OnClick="editEntry" runat="server" class="formbutton" Text="Edit" />
          <span id="eeResult" class="hidden" runat="server">Not done</span>
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
