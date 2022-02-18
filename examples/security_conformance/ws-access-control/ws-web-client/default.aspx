<%@ Page Language="C#" %>
<script runat="server">      

  protected void processLogin(Object s, EventArgs e) { 
    Server.Transfer("read.aspx?user=" + name.Text, true);
  }
</script><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
  <title>Healthcare - Login</title>
  <link rel="stylesheet" href="blue.css" type="text/css" />
  <link rel="stylesheet" href="styles.css" type="text/css" />
</head>
<body>
<div id="wrap">
  <div id="header">
    <div id="header-text">
      <h1><a href="#">Health<span>care</span></a></h1>
      <h2>Login</h2>
    </div>
  </div>

  <div id="content">
    <div id="page">
      <form id="form" method="post" runat="server">
      <fieldset>
        <legend>Login</legend>
        <div><label for="name">Username</label>
        <asp:TextBox id="name" runat="server" /></div>
        <asp:Button id="login" OnClick="processLogin" runat="server" class="formbutton" Text="Login" />
      </fieldset>
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
