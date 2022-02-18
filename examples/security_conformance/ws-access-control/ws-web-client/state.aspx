<%@ Page Language="C#" %>
<script runat="server">      
  string view;
  logic.View ViewState;
  int id;

  protected void Page_Init(Object s, EventArgs e) { 
    view = Request.QueryString["view"];
    ViewState = logic.determinateView(view);
    id        = Convert.ToInt32(Request.QueryString["id"]);
  }
</script><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
  <title>Healthcare - View State</title>
  <link rel="stylesheet" href="blue.css" type="text/css" />
  <link rel="stylesheet" href="styles.css" type="text/css" />
</head>
<body>
<div id="wrap">
  <div id="header">
    <div id="header-text">
      <h1><a href="#">Health<span>care</span></a></h1>
      <h2>View State</h2>
    </div>
  </div>

<!--
  <div id="navigation">
    <ul>
      <%= logic.createViewLink(view) %>
    </ul>
  </div>
-->

  <div id="content">
    <div>
      <%= logic.showAt(logic.View.LR | logic.View.ALL, ViewState, logic.printLrTable()) %>

      <div style="clear:left" />
<%--
      <%= logic.showAt(logic.View.SCR, ViewState, logic.printSCRidLinks()) %>
      <%= logic.showAt(logic.View.SCR, ViewState, logic.printScrTable(id)) %>
--%>
      <%= logic.showAt(logic.View.ALL, ViewState, logic.printScrTables()) %>
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
