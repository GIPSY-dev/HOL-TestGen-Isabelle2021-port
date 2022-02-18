<%@ WebService language="C#" class="HealthCare" %>

using System;
using System.Web.Services;
using System.Web.Services.Protocols;
using System.Collections.Generic;


using ScrID       = System.Int32;
using UserID      = System.Int32;
using UserRole    = System.String;
using LrID        = System.Int32;
using EntryID     = System.Int32;
using EntryStatus = System.String;


[WebService(Namespace="http://localhost/WebServices/")]
public class HealthCare : WebService {
  // State of the server
  //  needs to be static because a new HealthCare object is created for each
  //  request
  private static core.WState state = main.initialState;

  // Run the argument in the W monad with the current state and store the
  // new state
  private T runWMonad<T>(core.W<T> w, UserID id, UserRole role) {
    core.WRead wr = core.createWRead(id, transport.toUserRole(role));
    core.WResult<T> r = core.runW(wr, state, w);
    state = r.state;
    return r.value;
  }

  [WebMethod]
  public void reset() {
    state = main.initialState;
  }

  [WebMethod]
  public void createSCR(UserID userID, UserRole role, ScrID ScrID) {
    runWMonad(main.createSCR(ScrID), userID, role);
  }

  [WebMethod]
  public void appendEntry(UserID userID, UserRole role, ScrID ScrID,
                          EntryID entryID, EntryStatus status, UserID creator,
                          String data) {
    runWMonad(main.appendEntry(ScrID, entryID,
                               transport.toEntryStatus(status), creator, data),
              userID, role);
  }

  [WebMethod]
  public void deleteEntry(UserID userID, UserRole role, ScrID ScrID,
                          EntryID entryID) {
    runWMonad(main.deleteEntry(ScrID, entryID), userID, role);
  }

  [WebMethod]
  public String readEntry(UserID userID, UserRole role, ScrID ScrID,
                          EntryID entryID) {
    return runWMonad(main.readEntry(ScrID, entryID), userID, role);
  }

  [WebMethod]
  public String[] readSCR(UserID userID, UserRole role, ScrID ScrID) {
    return runWMonad(main.readScr(ScrID), userID, role);
  }

  [WebMethod]
  public void addLR(UserID userID, UserRole role, LrID LrID, ScrID LRScrID,
                    UserID[] LRUserIDs) {
    runWMonad(main.addLR(LrID, LRScrID, LRUserIDs), userID, role);
  }

  [WebMethod]
  public void removeLR(UserID userID, UserRole role, LrID LrID) {
    runWMonad(main.removeLR(LrID), userID, role);
  }

  [WebMethod]
  public void changeStatus(UserID userID, UserRole role, ScrID ScrID,
                           EntryID entryID, EntryStatus status) {
    runWMonad(main.changeStatus(ScrID, entryID,
                                transport.toEntryStatus(status)),
              userID, role);
  }

  [WebMethod]
  public void deleteSCR(UserID userID, UserRole role, ScrID ScrID) {
    runWMonad(main.deleteSCR(ScrID), userID, role);
  }

  [WebMethod]
  public void editEntry(UserID userID, UserRole role, ScrID ScrID,
                        EntryID entryID, String data) {
    runWMonad(main.editEntry(ScrID, entryID, data), userID, role);
  }

  [WebMethod]
  public string dumpLRs(string template) {
    return main.dumpLRs(state, template);
  }

  [WebMethod]
  public ScrID[] dumpSCRids() {
    return main.dumpSCRids(state);
  }

  [WebMethod]
  public string dumpSCR(ScrID ScrID, string template) {
    return main.dumpSCR(state, ScrID, template);
  }
}
