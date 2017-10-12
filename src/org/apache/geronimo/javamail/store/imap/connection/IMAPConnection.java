/**
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.geronimo.javamail.store.imap.connection;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.mail.FetchProfile;
import javax.mail.Flags;
import javax.mail.Folder;
import javax.mail.MessagingException;
import javax.mail.Quota;
import javax.mail.UIDFolder;
import javax.mail.internet.InternetHeaders;
import javax.mail.search.SearchTerm;

import org.apache.geronimo.javamail.authentication.AuthenticatorFactory;
import org.apache.geronimo.javamail.authentication.ClientAuthenticator;
import org.apache.geronimo.javamail.authentication.LoginAuthenticator;
import org.apache.geronimo.javamail.authentication.PlainAuthenticator;
import org.apache.geronimo.javamail.store.imap.ACL;
import org.apache.geronimo.javamail.store.imap.IMAPFolder;
import org.apache.geronimo.javamail.store.imap.Rights;
import org.apache.geronimo.javamail.util.CommandFailedException;
import org.apache.geronimo.javamail.util.InvalidCommandException;
import org.apache.geronimo.javamail.util.MailConnection;
import org.apache.geronimo.javamail.util.ProtocolProperties;
import org.apache.geronimo.javamail.util.TraceInputStream;
import org.apache.geronimo.javamail.util.TraceOutputStream;
import org.apache.geronimo.mail.util.Base64;

/**
 * Simple implementation of IMAP transport.  Just does plain RFC977-ish
 * delivery.
 * <p/>
 * There is no way to indicate failure for a given recipient (it's possible to have a
 * recipient address rejected).  The sun impl throws exceptions even if others successful),
 * but maybe we do a different way...
 * <p/>
 *
 * @version $Rev: 739377 $ $Date: 2009-01-31 02:57:39 +0800 (鍛ㄥ叚, 31 涓�湀 2009) $
 */
public class IMAPConnection extends MailConnection {
    protected static final String CAPABILITY_LOGIN_DISABLED = "LOGINDISABLED";
    protected static final String CAPABILITY_COMPRESS_DEFLATE = "COMPRESS=DEFLATE";
    private static final String COMMAND_COMPRESS_DEFLATE = "COMPRESS DEFLATE";
    // The connection pool we're a member of.  This keeps holds most of the 
    // connnection parameter information for us. 
    protected IMAPConnectionPool pool; 
    
    // special input stream for reading individual response lines.
    protected IMAPResponseStream reader;

    // connection pool connections.
    protected long lastAccess = 0;
    // our handlers for any untagged responses
    protected LinkedList responseHandlers = new LinkedList();
    // the list of queued untagged responses.
    protected List queuedResponses = new LinkedList();
    // this is set on if we had a forced disconnect situation from 
    // the server. 
    protected boolean closed = false;

    private boolean useCompress = false;
    public String currentFolderName = null;
    private IMAPUntaggedResponseHandler idleHandler = null;
    /**
     * Normal constructor for an IMAPConnection() object.
     * 
     * @param props  The protocol properties abstraction containing our
     *               property modifiers.
     * @param pool
     */
    public IMAPConnection(ProtocolProperties props, IMAPConnectionPool pool) {
        super(props);
        this.pool = pool; 
    }

                          
    /**
     * Connect to the server and do the initial handshaking.
     *
     * @exception MessagingException
     */
    public boolean protocolConnect(String host, int port, String authid, String realm, String username, String password) throws MessagingException {
        this.serverHost = host; 
        this.serverPort = port; 
        this.realm = realm; 
        this.authid = authid; 
        this.username = username; 
        this.password = password; 
        
        boolean preAuthorized = false; 
        useCompress = false;
        boolean IMAP_COMPRESS = false; // true to use compression if available, false to never use compression
        String mode = System.getProperty("IMAP_COMPRESS");
        if(mode != null)
        	IMAP_COMPRESS = Boolean.parseBoolean(mode);
        try {
            // create socket and connect to server.
            getConnection();

            // we need to ask the server what its capabilities are.  This can be done 
            // before we login.  
            //getCapability();
            // do a preauthoriziation check. 
            if (extractResponse("PREAUTH") != null) {
                preAuthorized = true; 
            }
            
            // make sure we process these now
            processPendingResponses(); 

            // if we're not already using an SSL connection, and we have permission to issue STARTTLS, AND
            // the server supports this, then switch to TLS mode before continuing.
            if (!sslConnection && props.getBooleanProperty(MAIL_STARTTLS_ENABLE, false)){// && hasCapability(CAPABILITY_STARTTLS)) {
                // if the server supports TLS, then use it for the connection.
                // on our connection.
                
                // tell the server of our intention to start a TLS session
                sendSimpleCommand("STARTTLS");
                
                // The connection is then handled by the superclass level. 
                getConnectedTLSSocket();
                
                // create the special reader for pulling the responses.
                reader = new IMAPResponseStream(inputStream);

                // the IMAP spec states that the capability response is independent of login state or   
                // user, but I'm not sure I believe that to be the case.  It doesn't hurt to refresh 
                // the information again after establishing a secure connection. 
                //getCapability();
                // and we need to repeat this check. 
                if (extractResponse("PREAUTH") != null) {
                    preAuthorized = true; 
                }
            }
            
            // damn, no login required.  
            if (preAuthorized) {
                return true; 
            }
            
            // go login with the server 
            boolean loginOk = login(); 
            // the IMAP spec states that the capability response is independent of login state or   
            // user, but I'm not sure I believe that to be the case.  It doesn't hurt to refresh 
            // the information again after establishing a secure connection. 
            if(loginOk)
            	getCapability();

            if(loginOk && IMAP_COMPRESS)
            {//initialize compression
            	if(hasCapability(CAPABILITY_COMPRESS_DEFLATE))
            	{
                    try
                    {
                        IMAPTaggedResponse rsp = sendCommand(COMMAND_COMPRESS_DEFLATE);
                        if(rsp.isOK())
                        {
                        	useCompress = true;
                        	//resetup streams
                        	getConnectionStreams();
                        	reader = new IMAPResponseStream(inputStream);
                        }
                    }
                    catch (Exception e)
                    {
                    	debugOut("Unable to negotiate compression", e);
                    }
                               		
            	}
            }
            
            return loginOk;
        } catch (IOException e) {
            if (debug) {
                debugOut("I/O exception establishing connection", e);
            }
            throw new MessagingException("Connection error", e);
        }
        finally {
            // make sure the queue is cleared 
            processPendingResponses(); 
        }
    }

    /**
     * Update the last access time for the connection.
     */
    protected void updateLastAccess() {
        lastAccess = System.currentTimeMillis();
    }

    /**
     * Test if the connection has been sitting idle for longer than
     * the set timeout period.
     *
     * @param timeout The allowed "freshness" interval.
     *
     * @return True if the connection has been active within the required
     *         interval, false if it has been sitting idle for too long.
     */
    public boolean isStale(long timeout) {
        return (System.currentTimeMillis() - lastAccess) > timeout;
    }


    /**
     * Close the connection.  On completion, we'll be disconnected from
     * the server and unable to send more data.
     *
     * @exception MessagingException
     */
    public void close() throws MessagingException {
        // if we're already closed, get outta here.
        if (socket == null) {
            return;
        }
        try {
            // say goodbye
            logout();   
        } finally {
            // and close up the connection.  We do this in a finally block to make sure the connection
            // is shut down even if quit gets an error.
            closeServerConnection();
            // get rid of our response processor too. 
            reader = null; 
        }
    }


    /**
     * Create a transport connection object and connect it to the
     * target server.
     *
     * @exception MessagingException
     */
    protected void getConnection() throws IOException, MessagingException
    {
        // do all of the non-protocol specific set up.  This will get our socket established 
        // and ready use. 
        super.getConnection(); 
        // create the special reader for pulling the responses.
        reader = new IMAPResponseStream(inputStream);

        // set the initial access time stamp
        updateLastAccess();
    }


    /**
     * Process a simple command/response sequence between the
     * client and the server.  These are commands where the
     * client is expecting them to "just work", and also will not
     * directly process the reply information.  Unsolicited untagged
     * responses are dispatched to handlers, and a MessagingException
     * will be thrown for any non-OK responses from the server.
     *
     * @param data   The command data we're writing out.
     *
     * @exception MessagingException
     */
    public void sendSimpleCommand(String data) throws MessagingException {
    	sendSimpleCommand(data, null);
    }
    public void sendSimpleCommand(String data, IMAPFolder.IdleHook hook) throws MessagingException {
        // create a command object and issue the command with that. 
        IMAPCommand command = new IMAPCommand(objId, data); 
        sendSimpleCommand(command, hook); 
    }


    /**
     * Process a simple command/response sequence between the
     * client and the server.  These are commands where the
     * client is expecting them to "just work", and also will not
     * directly process the reply information.  Unsolicited untagged
     * responses are dispatched to handlers, and a MessagingException
     * will be thrown for any non-OK responses from the server.
     *
     * @param data   The command data we're writing out.
     *
     * @exception MessagingException
     */
    public void sendSimpleCommand(IMAPCommand data) throws MessagingException {
    	sendSimpleCommand(data, null);
    }
    public void sendSimpleCommand(IMAPCommand data, IMAPFolder.IdleHook hook) throws MessagingException {
        // the command sending process will raise exceptions for bad responses....
        // we just need to send the command and forget about it. 
        sendCommand(data, hook);
    }


    /**
     * Sends a  command down the socket, returning the server response.
     * 
     * @param data   The String form of the command.
     * 
     * @return The tagged response information that terminates the command interaction.
     * @exception MessagingException
     */
    public IMAPTaggedResponse sendCommand(String data) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, data); 
        return sendCommand(command); 
    }


    /**
     * Sends a  command down the socket, returning the server response.
     * 
     * @param data   An IMAPCommand object with the prepared command information.
     * 
     * @return The tagged (or continuation) response information that terminates the 
     *         command response sequence.
     * @exception MessagingException
     */
    public synchronized IMAPTaggedResponse sendCommand(IMAPCommand data) throws MessagingException {
    	return sendCommand(data, null);
    }
    public synchronized IMAPTaggedResponse sendCommand(IMAPCommand data, IMAPFolder.IdleHook hook) throws MessagingException {
        // check first 
        checkConnected(); 
        try {
//        	Thread t = Thread.currentThread();
//        	Logger.getAnonymousLogger().log(Level.INFO, "call sendCommand from Thread:"+t.getName()+":"+data.tag);
            // have the command write the command data.  This also prepends a tag. 
            data.writeTo(outputStream, this);
            outputStream.flush();
            if(hook != null)
            	hook.run();
            // update the activity timestamp
            updateLastAccess();
            // get the received response  
            return receiveResponse(); 
        } catch (IOException e) {
            throw new MessagingException(e.toString(), e);
        }
    }
    

    /**
     * Sends a  message down the socket and terminates with the
     * appropriate CRLF
     * 
     * @param data   The string data to send.
     * 
     * @return An IMAPTaggedResponse item returned from the server.
     * @exception MessagingException
     */
    public IMAPTaggedResponse sendLine(String data) throws MessagingException {
        return sendLine(data.getBytes()); 
    }
    

    /**
     * Sends a  message down the socket and terminates with the
     * appropriate CRLF
     * 
     * @param data   The array of data to send to the server.
     * 
     * @return The response item returned from the IMAP server.
     * @exception MessagingException
     */
    public IMAPTaggedResponse sendLine(byte[] data) throws MessagingException {
        return sendLine(data, 0, data.length); 
    }
    

    /**
     * Sends a  message down the socket and terminates with the
     * appropriate CRLF
     * 
     * @param data   The source data array.
     * @param offset The offset within the data array.
     * @param length The length of data to send.
     * 
     * @return The response line returned from the IMAP server. 
     * @exception MessagingException
     */
    public synchronized IMAPTaggedResponse sendLine(byte[] data, int offset, int length) throws MessagingException {
        // check first 
        checkConnected(); 
        
        try {
            outputStream.write(data, offset, length);
            outputStream.write(CR);
            outputStream.write(LF);
            outputStream.flush();
            // update the activity timestamp
            updateLastAccess();
            return receiveResponse(); 
        } catch (IOException e) {
            throw new MessagingException(e.toString(), e);
        }
    }

    
    /**
     * Get a reply line for an IMAP command.
     *
     * @return An IMAP reply object from the stream.
     */
    public IMAPTaggedResponse receiveResponse() throws MessagingException {
        while (true) {
            // read and parse a response from the server.
            IMAPResponse response = reader.readResponse();
            response.setConnection(this);
            // The response set is terminated by either a continuation response or a  
            // tagged response (we only have a single command active at one time). 
            if (response instanceof IMAPTaggedResponse) {
                // update the access time stamp for later timeout processing.
                updateLastAccess(); 
                IMAPTaggedResponse tagged = (IMAPTaggedResponse)response; 
                // we turn these into exceptions here, which means the issuer doesn't have to 
                // worry about checking status. 
                if (tagged.isBAD()) {
                    throw new InvalidCommandException("Unexpected command IMAP command error"); 
                }
                else if (tagged.isNO()) {
                    throw new CommandFailedException("Unexpected error executing IMAP command"); 
                }
                return tagged;                       
            }
            else {
                // all other unsolicited responses are either async status updates or 
                // additional elements of a command we just sent.  These will be processed 
                // either during processing of the command response, or at the end of the 
                // current command processing. 
            	IMAPUntaggedResponse rsp = (IMAPUntaggedResponse)response;
            	 if (rsp.isKeyword("BAD") || rsp.isKeyword("NO")) {
                     String message = ((IMAPServerStatusResponse)response).getMessage(); 
                    throw new MessagingException(message);
                 }
            	 if(idleHandler != null)
            		 idleHandler.handleResponse(rsp);
                queuePendingResponse(rsp); 
            }
        }
    }

    
    /**
     * Get the servers capabilities from the wire....
     */
    public void getCapability() throws MessagingException {
       sendCommand("CAPABILITY");
        // get the capabilities from the response.
        IMAPCapabilityResponse response = (IMAPCapabilityResponse)extractResponse("CAPABILITY"); 
        capabilities = response.getCapabilities(); 
        authentications = response.getAuthentications(); 
    }

    /**
     * Logs out from the server.                                     
     */
    public void logout() throws MessagingException {
        // We can just send the command and generally ignore the 
        // status response. 
        sendCommand("LOGOUT");
    }

    /**
     * Deselect a mailbox when a folder returns a connection.
     * 
     * @exception MessagingException
     */
    public void closeMailbox() throws MessagingException {
        // We can just send the command and generally ignore the 
        // status response. 
        sendCommand("CLOSE");
    }

    
    /**
     * Authenticate with the server, if necessary (or possible).
     * 
     * @return true if we were able to authenticate correctly, false for authentication failures.
     * @exception MessagingException
     */
    protected boolean login() throws MessagingException
    {
        // if no username or password, fail this immediately. 
        // the base connect property should resolve a username/password combo for us and 
        // try again. 
        if (username == null || password == null) {
            return false; 
        }
        
        // are we permitted to use SASL mechanisms?
        if (props.getBooleanProperty(MAIL_SASL_ENABLE, false)) {
            // we might be enable for SASL, but the client and the server might
            // not have any supported mechanisms in common.  Try again with another
            // mechanism.
            if (processSaslAuthentication()) {
                return true;
            }
        }
        
        // see if we're allowed to try login.
        // the server can choose to disable the LOGIN command.  If not disabled, try 
        // using LOGIN rather than AUTHENTICATE. 
        // 2011.07.12 this is the only one method implemented correctly in geronimo mail
//        if (!hasCapability(CAPABILITY_LOGIN_DISABLED)) {
            return processLogin(); 
//        }

        // see if we're allowed to try plain.
  /*      try
        {
	        if (!props.getBooleanProperty(MAIL_PLAIN_DISABLE, false) && supportsMechanism(AUTHENTICATION_PLAIN)) {
	        	System.err.println("PLAIN AUTHENTICATION required, but implementation has bug!!");
	            return processPlainAuthentication();
	        }
        }
        catch(MessagingException e)
        {
        	System.err.println(e.getMessage());
        }

        // see if we're allowed to try login.
        try
        {
	        if (!props.getBooleanProperty(MAIL_LOGIN_DISABLE, false) && supportsMechanism(AUTHENTICATION_LOGIN)) {
	            // no authzid capability with this authentication method.
	        	System.err.println("LOGIN AUTHENTICATION required, but implementation has bug!!");
	            return processLoginAuthentication();
	        }
        }
        catch(MessagingException e)
        {	
        	System.err.println(e.getMessage());
        }

        
       
        
        throw new MessagingException("No supported LOGIN methods enabled");*/ 
    }

    
    /**
     * Process SASL-type authentication.
     *
     * @return Returns true if the server support a SASL authentication mechanism and
     * accepted reponse challenges.
     * @exception MessagingException
     */
    protected boolean processSaslAuthentication() throws MessagingException {
        // if unable to get an appropriate authenticator, just fail it. 
        ClientAuthenticator authenticator = getSaslAuthenticator(); 
        if (authenticator == null) {
            return false; 
        }
        
        // go process the login.
        return processLogin(authenticator);
    }
    
    protected ClientAuthenticator getSaslAuthenticator() {
        return AuthenticatorFactory.getAuthenticator(props, selectSaslMechanisms(), serverHost, username, password, authid, realm); 
    }

    /**
     * Process SASL-type PLAIN authentication.
     *
     * @return Returns true if the login is accepted. 
     * @exception MessagingException
     */
    protected boolean processPlainAuthentication() throws MessagingException {
        // go process the login.
        return processLogin(new PlainAuthenticator(username, password));
    }


    /**
     * Process SASL-type LOGIN authentication.
     *
     * @return Returns true if the login is accepted. 
     * @exception MessagingException
     */
    protected boolean processLoginAuthentication() throws MessagingException {
        // go process the login.
        return processLogin(new LoginAuthenticator(username, password));
    }
    
    
    /**
     * Process a LOGIN using the LOGIN command instead of AUTHENTICATE. 
     * 
     * @return true if the command succeeded, false for any authentication failures. 
     * @exception MessagingException
     */
    protected boolean processLogin() throws MessagingException {
        // arguments are "LOGIN userid password"
        IMAPCommand command = new IMAPCommand(objId, "LOGIN");
        command.appendAtom(username); 
        command.appendAtom(password); 
        
        // go issue the command 
        try {
            sendCommand(command); 
        } catch (CommandFailedException e) {
            // we'll get a NO response for a rejected login
            return false; 
        }
        // seemed to work ok....
        return true;   
    }


    /**
     * Process a login using the provided authenticator object.
     * 
     * NB:  This method is synchronized because we have a multi-step process going on 
     * here.  No other commands should be sent to the server until we complete. 
     *
     * @return Returns true if the server support a SASL authentication mechanism and
     * accepted reponse challenges.
     * @exception MessagingException
     */
    protected synchronized boolean processLogin(ClientAuthenticator authenticator) throws MessagingException {
        if (debug) {
            debugOut("Authenticating for user: " + username + " using " + authenticator.getMechanismName());
        }

        IMAPCommand command = new IMAPCommand(objId, "AUTHENTICATE");
        // and tell the server which mechanism we're using.
        command.appendAtom(authenticator.getMechanismName());
        // send the command now
        
        try {
            IMAPTaggedResponse response = sendCommand(command);

            // now process the challenge sequence.  We get a 235 response back when the server accepts the
            // authentication, and a 334 indicates we have an additional challenge.
            while (true) {
                // this should be a continuation reply, if things are still good.
                if (response.isContinuation()) {
                    // we're passed back a challenge value, Base64 encoded.
                    byte[] challenge = response.decodeChallengeResponse();

                    // have the authenticator evaluate and send back the encoded response.
                    response = sendLine(Base64.encode(authenticator.evaluateChallenge(challenge)));
                }
                else {
                    // there are only two choices here, OK or a continuation.  OK means 
                    // we've passed muster and are in. 
                    return true; 
                }
            }
        } catch (CommandFailedException e ) {
            // a failure at any point in this process will result in a "NO" response.  
            // That causes an exception to get thrown, so just fail the login 
            // if we get one. 
            return false; 
        }
    }
    

    /**
     * Return the server host for this connection.
     *
     * @return The String name of the server host.
     */
    public String getHost() {
        return serverHost;
    }

    
    /**
     * Attach a handler for untagged responses to this connection.
     *
     * @param h      The new untagged response handler.
     */
    public synchronized void addResponseHandler(IMAPUntaggedResponseHandler h) {
        responseHandlers.add(h);
    }


    /**
     * Remove a response handler from the connection.
     *
     * @param h      The handler to remove.
     */
    public synchronized void removeResponseHandler(IMAPUntaggedResponseHandler h) {
        responseHandlers.remove(h);
    }


    /**
     * Add a response to the pending untagged response queue.
     *
     * @param response The response to add.
     */
    public synchronized void queuePendingResponse(IMAPUntaggedResponse response) {
        queuedResponses.add(response);
    }

    /**
     * Process any untagged responses in the queue.  This will clear out
     * the queue, and send each response to the registered
     * untagged response handlers.
     */
    public void processPendingResponses() throws MessagingException {
        List pendingResponses = null;
        List handlerList = null; 

        synchronized(this) {
            if (queuedResponses.isEmpty()) {
                return;
            }
            pendingResponses = queuedResponses;
            queuedResponses = new LinkedList();
            // get a copy of the response handlers so we can 
            // release the connection lock before broadcasting 
            handlerList = (List)responseHandlers.clone(); 
        }
        
        for (int i = 0; i < pendingResponses.size(); i++) {
            IMAPUntaggedResponse response = (IMAPUntaggedResponse)pendingResponses.get(i); 
            for (int j = 0; j < handlerList.size(); j++) {
                // broadcast to each handler.  If a handler returns true, then it 
                // handled whatever this message required and we should skip sending 
                // it to other handlers. 
                IMAPUntaggedResponseHandler h = (IMAPUntaggedResponseHandler)handlerList.get(j); 
                if (h.handleResponse(response)) { 
                    break; 
                }
            }
        }
    }
    
    /**
     * Extract a single response from the pending queue that 
     * match a give keyword type.  All matching responses 
     * are removed from the pending queue. 
     * 
     * @param type   The string name of the keyword.
     * 
     * @return A List of all matching queued responses. 
     */
    public IMAPUntaggedResponse extractResponse(String type) {
        Iterator i = queuedResponses.iterator(); 
        while (i.hasNext()) {
            IMAPUntaggedResponse response = (IMAPUntaggedResponse)i.next(); 
            // if this is of the target type, move it to the response set. 
            if (response.isKeyword(type)) {
                i.remove(); 
                return response;
            }
        }
        return null;  
    }
    
    /**
     * Extract all responses from the pending queue that 
     * match a give keyword type.  All matching responses 
     * are removed from the pending queue. 
     * 
     * @param type   The string name of the keyword.
     * 
     * @return A List of all matching queued responses. 
     */
    public List extractResponses(String type) {
        List responses = new ArrayList(); 
        
        Iterator i = queuedResponses.iterator(); 
        while (i.hasNext()) {
            IMAPUntaggedResponse response = (IMAPUntaggedResponse)i.next(); 
            // if this is of the target type, move it to the response set. 
            if (response.isKeyword(type)) {
                i.remove(); 
                responses.add(response); 
            }
        }
        return responses; 
    }
    
    
    /**
     * Extract all responses from the pending queue that 
     * are "FETCH" responses for a given message number.  All matching responses 
     * are removed from the pending queue. 
     * 
     * @param type   The string name of the keyword.
     * 
     * @return A List of all matching queued responses. 
     */
    public List<IMAPFetchResponse> extractFetchResponses(int sequenceNumber) {
        List<IMAPFetchResponse> responses = new ArrayList<IMAPFetchResponse>(); 
        
        Iterator i = queuedResponses.iterator(); 
        while (i.hasNext()) {
            IMAPUntaggedResponse response = (IMAPUntaggedResponse)i.next(); 
            // if this is of the target type, move it to the response set. 
            if (response.isKeyword("FETCH")) {
                IMAPFetchResponse fetch = (IMAPFetchResponse)response; 
                // a response for the correct message number?
                if (fetch.sequenceNumber == sequenceNumber) {
                    // pluck these from the list and add to the response set. 
                    i.remove(); 
                    responses.add((IMAPFetchResponse)response); 
                }
            }
        }
        return responses; 
    }
    
    /**
     * Extract a fetch response data item from the queued elements. 
     * 
     * @param sequenceNumber
     *               The message number we're interested in.  Fetch responses for other messages
     *               will be skipped.
     * @param type   The type of body element we need. It is assumed that only one item for
     *               the given message number will exist in the queue.  The located item will
     *               be returned, and that fetch response will be removed from the pending queue.
     * 
     * @return The target data item, or null if a match is not found.
     */
    protected IMAPFetchDataItem extractFetchDataItem(long sequenceNumber, int type) 
    {
        Iterator i = queuedResponses.iterator(); 
        while (i.hasNext()) {
            IMAPUntaggedResponse response = (IMAPUntaggedResponse)i.next(); 
            // if this is of the target type, move it to the response set. 
            if (response.isKeyword("FETCH")) {
                IMAPFetchResponse fetch = (IMAPFetchResponse)response; 
                // a response for the correct message number?
                if (fetch.sequenceNumber == sequenceNumber) {
                    // does this response have the item we're looking for?
                    IMAPFetchDataItem item = fetch.getDataItem(type); 
                    if (item != null) {
                        // remove this from the pending queue and return the 
                        // located item
                        i.remove(); 
                        return item; 
                    }
                }
            }
        }
        // not located, sorry 
        return null;       
    }
    
    /**
     * Extract a all fetch responses that contain a given data item.  
     * 
     * @param type   The type of body element we need. It is assumed that only one item for
     *               the given message number will exist in the queue.  The located item will
     *               be returned, and that fetch response will be removed from the pending queue.
     * 
     * @return A List of all matching Fetch responses.                         
     */
    protected List extractFetchDataItems(int type) 
    {
        Iterator i = queuedResponses.iterator(); 
        List items = new ArrayList(); 
        
        while (i.hasNext()) {
            IMAPUntaggedResponse response = (IMAPUntaggedResponse)i.next(); 
            // if this is of the target type, move it to the response set. 
            if (response.isKeyword("FETCH")) {
                IMAPFetchResponse fetch = (IMAPFetchResponse)response; 
                // does this response have the item we're looking for?
                IMAPFetchDataItem item = fetch.getDataItem(type); 
                if (item != null) {
                    // remove this from the pending queue and return the 
                    // located item
                    i.remove(); 
                    // we want the fetch response, not the data item, because 
                    // we're going to require the message sequence number information 
                    // too. 
                    items.add(fetch); 
                }
            }
        }
        // return whatever we have. 
        return items;      
    }

    /**
     * Make sure we have the latest status information available.  We
     * retreive this by sending a NOOP command to the server, and
     * processing any untagged responses we get back.
     */
    public void updateMailboxStatus() throws MessagingException {
        sendSimpleCommand("NOOP");
    }


    /**
     * check to see if this connection is truely alive.
     * 
     * @param timeout The timeout value to control how often we ping
     *                the server to see if we're still good.
     * 
     * @return true if the server is responding to requests, false for any
     *         connection errors.  This will also update the folder status
     *         by processing returned unsolicited messages.
     */
    public synchronized boolean isAlive(long timeout) {
        long lastUsed = System.currentTimeMillis() - lastAccess; 
        /*
         * LiuLele, Apr. 8, 2013, check socket to avoid the following exception
         * javax.mail.MessagingException: no connection
	at org.apache.geronimo.javamail.util.MailConnection.checkConnected(MailConnection.java:601) ~[geronimo-forgunte-mail.jar:na]
	at org.apache.geronimo.javamail.store.imap.connection.IMAPConnection.sendCommand(IMAPConnection.java:335) ~[geronimo-forgunte-mail.jar:na]
	at org.apache.geronimo.javamail.store.imap.connection.IMAPConnection.list(IMAPConnection.java:1183) ~[geronimo-forgunte-mail.jar:na]
	at org.apache.geronimo.javamail.store.imap.IMAPFolder.filterFolders(IMAPFolder.java:1970) ~[geronimo-forgunte-mail.jar:na]
	at org.apache.geronimo.javamail.store.imap.IMAPFolder.list(IMAPFolder.java:366) ~[geronimo-forgunte-mail.jar:na]
	at fortunedog.mail.proxy.ImapProtocol.listForders(ImapProtocol.java:540) [ImapProtocol.class:na]
	at fortunedog.mail.proxy.ImapProtocol.connect(ImapProtocol.java:432) [ImapProtocol.class:na]
	at fortunedog.mail.proxy.MailProtocol.checkNewMails(MailProtocol.java:84) [MailProtocol.class:na]
	at fortunedog.mail.proxy.MailClient.checkNewMails(MailClient.java:587) [MailClient.class:na]
	at fortunedog.mail.proxy.servlet.SyncupMail.dbService(SyncupMail.java:72) [SyncupMail.class:na]
	at fortunedog.mail.proxy.servlet.DatabaseServlet.service(DatabaseServlet.java:66) [DatabaseServlet.class:na]
         */
        if(socket == null || !socket.isConnected())
        	return false;
        if (lastUsed < timeout) {
            return true; 
        }
        
        try {
            sendSimpleCommand("NOOP"); 
            return true;
        } catch (MessagingException e) {
            // the NOOP command will throw a MessagingException if we get anything 
            // other than an OK response back from the server.  
        }
        return false;
    }


    /**
     * Issue a fetch command to retrieve the message ENVELOPE structure.
     *
     * @param sequenceNumber The sequence number of the message.
     *
     * @return The IMAPResponse item containing the ENVELOPE information.
     */
    public synchronized List fetchEnvelope(int sequenceNumber) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber);
        command.startList(); 
        command.appendAtom("ENVELOPE INTERNALDATE RFC822.SIZE"); 
        command.endList();   
        
        // we want all of the envelope information about the message, which involves multiple FETCH chunks.
        sendCommand(command);
        // these are fairly involved sets, so the caller needs to handle these.
        // we just return all of the FETCH results matching the target message number.  
        return extractFetchResponses(sequenceNumber); 
    }
    
    /**
     * Issue a FETCH command to retrieve the message BODYSTRUCTURE structure.
     *
     * @param sequenceNumber The sequence number of the message.
     *
     * @return The IMAPBodyStructure item for the message.
     *         All other untagged responses are queued for processing.
     */
    public synchronized IMAPBodyStructure fetchBodyStructure(int sequenceNumber) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber);
        command.startList(); 
        command.appendAtom("BODYSTRUCTURE"); 
        command.endList();   
        
        // we want all of the envelope information about the message, which involves multiple FETCH chunks.
        sendCommand(command);
        // locate the response from this 
        IMAPBodyStructure bodyStructure = (IMAPBodyStructure)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.BODYSTRUCTURE);

        if (bodyStructure == null) {
            throw new MessagingException("No BODYSTRUCTURE information received from IMAP server");
        }
        // and return the body structure directly.
        return bodyStructure;
    }


    /**
     * Issue a FETCH command to retrieve the message RFC822.HEADERS structure containing the message headers (using PEEK).
     *
     * @param sequenceNumber The sequence number of the message.
     *
     * @return The IMAPRFC822Headers item for the message.
     *         All other untagged responses are queued for processing.
     */
    public synchronized InternetHeaders fetchHeaders(int sequenceNumber, String part) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber);
        command.startList(); 
        command.appendAtom("BODY.PEEK"); 
        command.appendBodySection(part, "HEADER"); 
        command.endList();   
        
        // we want all of the envelope information about the message, which involves multiple FETCH chunks.
        sendCommand(command);
        IMAPInternetHeader header = (IMAPInternetHeader)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.HEADER);

        if (header == null) {
            throw new MessagingException("No HEADER information received from IMAP server");
        }
        // and return the body structure directly.
        return header.headers;
    }


    /**
     * Issue a FETCH command to retrieve the message text
     *
     * @param sequenceNumber The sequence number of the message.
     *
     * @return The IMAPMessageText item for the message.
     *         All other untagged responses are queued for processing.
     */
    public synchronized IMAPMessageText fetchText(int sequenceNumber) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber);
        command.startList(); 
        command.appendAtom("BODY.PEEK"); 
        command.appendBodySection("TEXT"); 
        command.endList();   
        
        // we want all of the envelope information about the message, which involves multiple FETCH chunks.
        sendCommand(command);
        IMAPMessageText text = (IMAPMessageText)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.TEXT);

        if (text == null) {
            throw new MessagingException("No TEXT information received from IMAP server");
        }
        // and return the body structure directly.
        return text;
    }

    public synchronized List<IMAPFetchDataItem> fetchEntireMessage(int sequenceNumber) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber);
        command.startList(); 
        command.appendAtom("BODY.PEEK"); 
        command.appendBodySection(""); 
        command.endList();   
        
        // we want all of the envelope information about the message, which involves multiple FETCH chunks.
        sendCommand(command);
        List<IMAPFetchDataItem> rst = new ArrayList<IMAPFetchDataItem>();
        List<IMAPFetchResponse> rsp = extractFetchResponses(sequenceNumber);
        for(IMAPFetchResponse r : rsp)
        {
        	List<IMAPFetchDataItem> items = r.getDataItems(); 
        	rst.addAll(items);
        }
        return rst;
    }

    /**
     * Issue a FETCH command to retrieve the message text
     *
     * @param sequenceNumber The sequence number of the message.
     *
     * @return The IMAPMessageText item for the message.
     *         All other untagged responses are queued for processing.
     */
    public synchronized IMAPMessageText fetchBodyPartText(int sequenceNumber, String section) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber);
        command.startList(); 
        command.appendAtom("BODY.PEEK"); 
        command.appendBodySection(section, "TEXT"); 
        command.endList();   
        
        // we want all of the envelope information about the message, which involves multiple FETCH chunks.
        sendCommand(command);
        IMAPMessageText text = (IMAPMessageText)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.TEXT);

        if (text == null) {
            throw new MessagingException("No TEXT information received from IMAP server");
        }
        // and return the body structure directly.
        return text;
    }


    /**
     * Issue a FETCH command to retrieve the entire message body in one shot.
     * This may also be used to fetch an embedded message part as a unit.
     * 
     * @param sequenceNumber
     *                The sequence number of the message.
     * @param section The section number to fetch.  If null, the entire body of the message
     *                is retrieved.
     * 
     * @return The IMAPBody item for the message.
     *         All other untagged responses are queued for processing.
     * @exception MessagingException
     */
    public synchronized IMAPBody fetchBody(int sequenceNumber, String section) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber);
        command.startList(); 
        command.appendAtom("BODY.PEEK"); 
        // no part name here, only the section identifier.  This will fetch 
        // the entire body, with all of the bits in place. 
        command.appendBodySection(section, null); 
        command.endList();   
        
        // we want all of the envelope information about the message, which involves multiple FETCH chunks.
        sendCommand(command);
        IMAPBody body = (IMAPBody)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.BODY);

        if (body == null) {
            throw new MessagingException("No BODY information received from IMAP server");
        }
        // and return the body structure directly.
        return body;
    }
    
    
    /**
     * Fetch the message content.  This sorts out which method should be used 
     * based on the server capability.
     * 
     * @param sequenceNumber
     *               The sequence number of the target message.
     * 
     * @return The byte[] content information.
     * @exception MessagingException
     */
    public byte[] fetchContent(int sequenceNumber) throws MessagingException {
        // fetch the text item and return the data 
        IMAPMessageText text = fetchText(sequenceNumber);
        return text.getContent();
    }
    
    
    /**
     * Fetch the message content.  This sorts out which method should be used 
     * based on the server capability.
     * 
     * @param sequenceNumber
     *               The sequence number of the target message.
     * 
     * @return The byte[] content information.
     * @exception MessagingException
     */
    public byte[] fetchContent(int sequenceNumber, String section) throws MessagingException {
        if (section == null) {
            IMAPMessageText text = fetchText(sequenceNumber);
            return text.getContent();
        } else {
   //     	IMAPBody body = fetchBody(sequenceNumber, section);
    //		return body.getContent();
        	try
        	{
        		IMAPBody body = fetchBody(sequenceNumber, section);
        		return body.getContent();
        	}
        	catch(MessagingException except)
        	{
        		//Tim Liu add 2012.01.14 
        		IMAPMessageText text = (IMAPMessageText)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.TEXT);
        		return text.getContent();
        	}
            
        }
    }


    /**
     * Send an LIST command to the IMAP server, returning all LIST
     * response information.
     *
     * @param mailbox The reference mailbox name sent on the command.
     * @param pattern The match pattern used on the name.
     *
     * @return A List of all LIST response information sent back from the server.
     */
    public synchronized List list(String mailbox, String pattern) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "LIST");

        // construct the command, encoding the tokens as required by the content.
        command.appendEncodedString(mailbox);
        command.appendEncodedString(pattern);
        
        sendCommand(command);
        
        // pull out the ones we're interested in 
        return extractResponses("LIST"); 
    }


    /**
     * Send an LSUB command to the IMAP server, returning all LSUB
     * response information.
     *
     * @param mailbox The reference mailbox name sent on the command.
     * @param pattern The match pattern used on the name.
     *
     * @return A List of all LSUB response information sent back from the server.
     */
    public List listSubscribed(String mailbox, String pattern) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "LSUB");

        // construct the command, encoding the tokens as required by the content.
        command.appendEncodedString(mailbox);
        command.appendEncodedString(pattern);

        sendCommand(command);
        // pull out the ones we're interested in 
        return extractResponses("LSUB"); 
    }


    /**
     * Subscribe to a give mailbox.
     *
     * @param mailbox The desired mailbox name.
     *
     * @exception MessagingException
     */
    public void subscribe(String mailbox) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "SUBSCRIBE");
        // add on the encoded mailbox name, as the appropriate token type.
        command.appendEncodedString(mailbox);

        // send this, and ignore the response.
        sendSimpleCommand(command);
    }


    /**
     * Unsubscribe from a mailbox.
     *
     * @param mailbox The mailbox to remove.
     *
     * @exception MessagingException
     */
    public void unsubscribe(String mailbox) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "UNSUBSCRIBE");
        // add on the encoded mailbox name, as the appropriate token type.
        command.appendEncodedString(mailbox);

        // send this, and ignore the response.
        sendSimpleCommand(command);
    }


    /**
     * Create a mailbox.
     *
     * @param mailbox The desired new mailbox name (fully qualified);
     *
     * @exception MessagingException
     */
    public void createMailbox(String mailbox) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "CREATE");
        // add on the encoded mailbox name, as the appropriate token type.
        command.appendEncodedString(mailbox);

        // send this, and ignore the response.
        sendSimpleCommand(command);
    }


    /**
     * Delete a mailbox.
     *
     * @param mailbox The target mailbox name (fully qualified);
     *
     * @exception MessagingException
     */
    public void deleteMailbox(String mailbox) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "DELETE");
        // add on the encoded mailbox name, as the appropriate token type.
        command.appendEncodedString(mailbox);

        // send this, and ignore the response.
        sendSimpleCommand(command);
    }


    /**
     * Rename a mailbox.
     *
     * @param mailbox The target mailbox name (fully qualified);
     *
     * @exception MessagingException
     */
    public void renameMailbox(String oldName, String newName) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "RENAME");
        // add on the encoded mailbox name, as the appropriate token type.
        command.appendEncodedString(oldName);
        command.appendEncodedString(newName);

        // send this, and ignore the response.
        sendSimpleCommand(command);
    }


    /**
     * Retrieve a complete set of status items for a mailbox.
     *
     * @param mailbox The mailbox name.
     *
     * @return An IMAPMailboxStatus item filled in with the STATUS responses.
     * @exception MessagingException
     */
    public synchronized IMAPMailboxStatus getMailboxStatus(String mailbox) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "STATUS");

        // construct the command, encoding the tokens as required by the content.
        command.appendEncodedString(mailbox);
        // request all of the status items
        command.append(" (MESSAGES RECENT UIDNEXT UIDVALIDITY UNSEEN)");

        sendCommand(command);

        // now harvest each of the respon
        IMAPMailboxStatus status = new IMAPMailboxStatus();
        status.mergeSizeResponses(extractResponses("EXISTS")); 
        status.mergeSizeResponses(extractResponses("RECENT")); 
        status.mergeOkResponses(extractResponses("UIDNEXT")); 
        status.mergeOkResponses(extractResponses("UIDVALIDITY")); 
        status.mergeOkResponses(extractResponses("UNSEEN")); 
        status.mergeStatus((IMAPStatusResponse)extractResponse("STATUS")); 
        status.mergeStatus((IMAPPermanentFlagsResponse)extractResponse("PERMANENTFLAGS")); 

        return status;
    }


    /**
     * Select a mailbox, returning the accumulated status information
     * about the mailbox returned with the response.
     *
     * @param mailbox  The desired mailbox name.
     * @param readOnly The open mode.  If readOnly is true, the mailbox is opened
     *                 using EXAMINE rather than SELECT.
     *
     * @return A status object containing the mailbox particulars.
     * @exception MessagingException
     */
    public synchronized IMAPMailboxStatus openMailbox(String mailbox, boolean readOnly) throws MessagingException {
    	currentFolderName = null;
    	IMAPCommand command = new IMAPCommand(objId);

        // if readOnly is required, we use EXAMINE to switch to the mailbox rather than SELECT.
        // This returns the same response information, but the mailbox will not accept update operations.
        if (readOnly) {
            command.appendAtom("EXAMINE");
        }
        else {
            command.appendAtom("SELECT");
        }

        // construct the command, encoding the tokens as required by the content.
        command.appendEncodedString(mailbox);

        // issue the select
        IMAPTaggedResponse response = sendCommand(command);

        IMAPMailboxStatus status = new IMAPMailboxStatus(); 
        // set the mode to the requested open mode. 
        status.mode = readOnly ? Folder.READ_ONLY : Folder.READ_WRITE; 
        
        // the server might disagree on the mode, so check to see if 
        // it's telling us READ-ONLY.  
        if (response.hasStatus("READ-ONLY")) {
            status.mode = Folder.READ_ONLY; 
        }
        
        // some of these are required, some are optional. 
        status.mergeFlags((IMAPFlagsResponse)extractResponse("FLAGS")); 
        status.mergeStatus((IMAPSizeResponse)extractResponse("EXISTS")); 
        status.mergeStatus((IMAPSizeResponse)extractResponse("RECENT")); 
        status.mergeStatus((IMAPOkResponse)extractResponse("UIDVALIDITY")); 
        status.mergeStatus((IMAPOkResponse)extractResponse("UNSEEN")); 
        status.mergeStatus((IMAPPermanentFlagsResponse)extractResponse("PERMANENTFLAGS")); 
        // mine the response for status information about the selected mailbox.
        currentFolderName = mailbox;
        return status; 
    }


    /**
     * Tells the IMAP server to expunge messages marked for deletion.
     * The server will send us an untagged EXPUNGE message back for
     * each deleted message.  For explicit expunges we request, we'll
     * grabbed the untagged responses here, rather than force them to 
     * be handled as pending responses.  The caller will handle the 
     * updates directly. 
     *
     * @exception MessagingException
     */
    public synchronized List expungeMailbox() throws MessagingException {
        // send the message, and make sure we got an OK response 
        sendCommand("EXPUNGE");
        // extract all of the expunged responses and return. 
        return extractResponses("EXPUNGED"); 
    }

    public long[] searchMailbox(SearchTerm term) throws MessagingException {
        return searchMailbox("ALL", term);
    }

    /**
     * Send a search to the IMAP server using the specified
     * messages selector and search term.  This figures out what
     * to do with CHARSET on the SEARCH command.
     *
     * @param messages The list of messages (comma-separated numbers or "ALL").
     * @param term     The desired search criteria
     *
     * @return Returns an int[] array of message numbers for all matched messages.
     * @exception MessagingException
     */
    public long[] searchMailbox(String messages, SearchTerm term) throws MessagingException {
        // don't use a charset by default, but we need to look at the data to see if we have a problem.
        String charset = null;

        if (IMAPCommand.checkSearchEncoding(term)) {
            // not sure exactly how to decide what to use here.  Two immediate possibilities come to mind,
            // UTF-8 or the MimeUtility.getDefaultJavaCharset() value.  Running a small test against the
            // Sun impl shows them sending a CHARSET value of UTF-8, so that sounds like the winner.  I don't
            // believe there's anything in the CAPABILITY response that would tell us what to use.
            charset = "UTF-8";
        }

        return searchMailbox(messages, term, charset);
    }

    /**
     * Send a search to the IMAP server using the specified
     * messages selector and search term.
     *
     * @param messages The list of messages (comma-separated numbers or "ALL").
     * @param charset  The charset specifier to send to the server.  If null, then
     *                 the CHARSET keyword is omitted.
     * @param term     The desired search criteria
     *
     * @return Returns an int[] array of message numbers for all matched messages.
     * @exception MessagingException
     */
    public synchronized long[] searchMailbox(String messages, SearchTerm term, String charset) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "SEARCH");

        // if we have an explicit charset to use, append that.
        if (charset != null) {
            command.appendAtom("CHARSET");
            command.appendAtom(charset);
        }

        // now go through the process of translating the javamail SearchTerm objects into
        // the IMAP command sequence.  The SearchTerm sequence may be a complex tree of comparison terms,
        // so this is not a simple process.
        if(term != null)
        	command.appendSearchTerm(term, charset);
        // need to append the message set 
        command.appendAtom(messages); 

        // now issue the composed command.
        sendCommand(command);

        // get the list of search responses 
        IMAPSearchResponse hits = (IMAPSearchResponse)extractResponse("SEARCH"); 
        // and return the message hits 
        return hits.messageNumbers; 
    }


    /**
     * Append a message to a mailbox, given the direct message data.
     *
     * @param mailbox The target mailbox name.
     * @param messageFlags
     *                The initial flag set for the appended message.
     * @param messageDate
     *                The received date the message is created with,
     * @param messageData
     *                The RFC822 Message data stored on the server.
     *
     * @exception MessagingException
     */
    public void appendMessage(String mailbox, Date messageDate, Flags messageFlags, byte[] messageData) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "APPEND");

        // the mailbox is encoded.
        command.appendEncodedString(mailbox);

        if (messageFlags != null) {
            // the flags are pulled from an existing object.  We can set most flag values, but the servers
            // reserve RECENT for themselves.  We need to force that one off.
            messageFlags.remove(Flags.Flag.RECENT);
            // and add the flag list to the commmand.
            command.appendFlags(messageFlags);
        }

        if (messageDate != null) {
            command.appendDate(messageDate);
        }

        // this gets appended as a literal.
        command.appendLiteral(messageData);
        // just send this as a simple command...we don't deal with the response other than to verifiy
        // it was ok.
        sendSimpleCommand(command);
    }

    /**
     * Fetch the flag set for a given message sequence number.
     * 
     * @param sequenceNumber
     *               The message sequence number.
     * 
     * @return The Flags defined for this message.
     * @exception MessagingException
     */
    public synchronized Flags fetchFlags(int sequenceNumber) throws MessagingException { 
        // we want just the flag item here.  
        sendCommand("FETCH " + String.valueOf(sequenceNumber) + " (FLAGS)");
        // get the return data item, and get the flags from within it
        IMAPFlags flags = (IMAPFlags)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.FLAGS);
        return flags.flags; 
    }
    

    /**
     * Set the flags for a range of messages.
     * 
     * @param messageSet The set of message numbers.
     * @param flags      The new flag settings.
     * @param set        true if the flags should be set, false for a clear operation.
     * 
     * @return A list containing all of the responses with the new flag values.
     * @exception MessagingException
     */
    public synchronized List setFlags(String messageSet, Flags flags, boolean set) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "STORE");
        command.appendAtom(messageSet);
        // the command varies depending on whether this is a set or clear operation
        if (set) {
            command.appendAtom("+FLAGS");
        }
        else {
            command.appendAtom("-FLAGS");
        }

        // append the flag set
        command.appendFlags(flags);
        
        // we want just the flag item here.  
        sendCommand(command); 
        // we should have a FETCH response for each of the updated messages.  Return this 
        // response, and update the message numbers. 
        return extractFetchDataItems(IMAPFetchDataItem.FLAGS);
    }
    

    /**
     * Set the flags for a single message.
     * 
     * @param sequenceNumber
     *               The sequence number of target message.
     * @param flags  The new flag settings.
     * @param set    true if the flags should be set, false for a clear operation.
     * 
     * @exception MessagingException
     */
    public synchronized Flags setFlags(int sequenceNumber, Flags flags, boolean set) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "STORE");
        command.appendInteger(sequenceNumber); 
        // the command varies depending on whether this is a set or clear operation
        if (set) {
            command.appendAtom("+FLAGS");
        }
        else {
            command.appendAtom("-FLAGS");
        }

        // append the flag set
        command.appendFlags(flags);
        
        // we want just the flag item here.  
        sendCommand(command); 
        // get the return data item, and get the flags from within it
        IMAPFlags flagResponse = (IMAPFlags)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.FLAGS);
        return flagResponse.flags; 
    }


    /**
     * Copy a range of messages to a target mailbox. 
     * 
     * @param messageSet The set of message numbers.
     * @param target     The target mailbox name.
     * 
     * @exception MessagingException
     */
    public void copyMessages(String messageSet, String target) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "COPY");
        // the auth command initiates the handshaking.
        command.appendAtom(messageSet);
        // the mailbox is encoded.
        command.appendEncodedString(target);
        // just send this as a simple command...we don't deal with the response other than to verifiy
        // it was ok.
        sendSimpleCommand(command);
    }
    
    
    /**
     * Fetch the message number for a give UID.
     * 
     * @param uid    The target UID
     * 
     * @return An IMAPUid object containing the mapping information.
     */
    public synchronized IMAPUid getSequenceNumberForUid(long uid) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "UID FETCH");
        command.appendLong(uid);
        command.appendAtom("(UID)"); 

        // this situation is a little strange, so it deserves a little explanation.  
        // We need the message sequence number for this message from a UID value.  
        // we're going to send a UID FETCH command, requesting the UID value back.
        // That seems strange, but the * nnnn FETCH response for the request will 
        // be tagged with the message sequence number.  THAT'S the information we 
        // really want, and it will be included in the IMAPUid object. 

        sendCommand(command);
        // ok, now we need to search through these looking for a FETCH response with a UID element.
        List responses = extractResponses("FETCH"); 

        // we're looking for a fetch response with a UID data item with the UID information 
        // inside of it. 
        for (int i = 0; i < responses.size(); i++) {
            IMAPFetchResponse response = (IMAPFetchResponse)responses.get(i); 
            IMAPUid item = (IMAPUid)response.getDataItem(IMAPFetchDataItem.UID); 
            // is this the response we're looking for?  The information we 
            // need is the message number returned with the response, which is 
            // also contained in the UID item. 
            if (item != null && item.uid == uid) {
                return item; 
            }
            // not one meant for us, add it back to the pending queue. 
            queuePendingResponse(response);
        }
        // didn't find this one 
        return null; 
    }
    
    
    /**
     * Fetch the message numbers for a consequetive range 
     * of UIDs.
     * 
     * @param start  The start of the range.
     * @param end    The end of the uid range.
     * 
     * @return A list of UID objects containing the mappings.  
     */
    public synchronized List<IMAPUid> getSequenceNumbersForUids(long start, long end) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "UID FETCH");
        // send the request for the range "start:end" so we can fetch all of the info 
        // at once. 
        command.appendLong(start);
        command.append(":"); 
        // not the special range marker?  Just append the 
        // number.  The LASTUID value needs to be "*" on the command. 
        if (end != UIDFolder.LASTUID) {
            command.append(end+"");
        }
        else {
            command.append("*");
        }
        command.appendAtom("(UID)"); 

        // this situation is a little strange, so it deserves a little explanation.  
        // We need the message sequence number for this message from a UID value.  
        // we're going to send a UID FETCH command, requesting the UID value back.
        // That seems strange, but the * nnnn FETCH response for the request will 
        // be tagged with the message sequence number.  THAT'S the information we 
        // really want, and it will be included in the IMAPUid object. 

        sendCommand(command);
        // ok, now we need to search through these looking for a FETCH response with a UID element.
        List responses = extractResponses("FETCH"); 

  //      List uids = new ArrayList(Math.max(10,(int)(end - start + 1))); 
        List<IMAPUid> uids = new LinkedList<IMAPUid>(); 

        // we're looking for a fetch response with a UID data item with the UID information 
        // inside of it. 
        for (int i = 0; i < responses.size(); i++) {
            IMAPFetchResponse response = (IMAPFetchResponse)responses.get(i); 
            IMAPUid item = (IMAPUid)response.getDataItem(IMAPFetchDataItem.UID); 
            // is this the response we're looking for?  The information we 
            // need is the message number returned with the response, which is 
            // also contained in the UID item. 
            if (item != null) {
                uids.add(item); 
            }
            else {
                // not one meant for us, add it back to the pending queue. 
                queuePendingResponse(response);
            }
        }
        // return the list of uids we located. 
        return uids; 
    }
    
    
    /**
     * Fetch the UID value for a target message number
     * 
     * @param sequenceNumber
     *               The target message number.
     * 
     * @return An IMAPUid object containing the mapping information.
     */
    public synchronized IMAPUid getUidForSequenceNumber(int sequenceNumber) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendInteger(sequenceNumber); 
        command.appendAtom("(UID)"); 

        // similar to the other fetches, but without the strange bit.  We're starting 
        // with the message number in this case. 

        sendCommand(command);
        
        // ok, now we need to search through these looking for a FETCH response with a UID element.
        return (IMAPUid)extractFetchDataItem(sequenceNumber, IMAPFetchDataItem.UID); 
    }
    
    
    /**
     * Retrieve the user name space info from the server.
     * 
     * @return An IMAPNamespace response item with the information.  If the server 
     *         doesn't support the namespace extension, an empty one is returned.
     */
    public synchronized IMAPNamespaceResponse getNamespaces() throws MessagingException {
        // if no namespace capability, then return an empty 
        // response, which will trigger the default behavior. 
        /*if (!hasCapability("NAMESPACE")) {
            return new IMAPNamespaceResponse(); 
        }*/
        // no arguments on this command, so just send an hope it works. 
        sendCommand("NAMESPACE"); 
        
        // this should be here, since it's a required response when the  
        // command worked.  Just extract, and return. 
        return (IMAPNamespaceResponse)extractResponse("NAMESPACE"); 
    }
    
    
    /**
     * Prefetch message information based on the request profile.  We'll return
     * all of the fetch information to the requesting Folder, which will sort 
     * out what goes where. 
     * 
     * @param messageSet The set of message numbers we need to fetch.
     * @param profile    The profile of the required information.
     * 
     * @return All FETCH responses resulting from the command. 
     * @exception MessagingException
     */
    public synchronized List fetch(String messageSet, FetchProfile profile) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "FETCH");
        command.appendAtom(messageSet); 
        // this is the set of items to append           
        command.appendFetchProfile(profile); 
    
        // now send the fetch command, which will likely send back a lot of "FETCH" responses. 
        // Suck all of those reponses out of the queue and send them back for processing. 
        sendCommand(command); 
        // we can have a large number of messages here, so just grab all of the fetches 
        // we get back, and let the Folder sort out who gets what. 
        return extractResponses("FETCH"); 
    }
    
    
    /**
     * Set the ACL rights for a mailbox.  This replaces 
     * any existing ACLs defined.
     * 
     * @param mailbox The target mailbox.
     * @param acl     The new ACL to be used for the mailbox.
     * 
     * @exception MessagingException
     */
    public synchronized void setACLRights(String mailbox, ACL acl) throws MessagingException {
        IMAPCommand command = new IMAPCommand(objId, "SETACL");
        command.appendEncodedString(mailbox);
        
        command.appendACL(acl); 
        
        sendSimpleCommand(command); 
    }
    
    
    /**
     * Add a set of ACL rights to a mailbox.
     * 
     * @param mailbox The mailbox to alter.
     * @param acl     The ACL to add.
     * 
     * @exception MessagingException
     */
    public synchronized void addACLRights(String mailbox, ACL acl) throws MessagingException {
       /* if (!hasCapability("ACL")) {
            throw new MethodNotSupportedException("ACL not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "SETACL");
        command.appendEncodedString(mailbox);
        
        command.appendACL(acl, "+"); 
        
        sendSimpleCommand(command); 
    }
    
    
    /**
     * Remove an ACL from a given mailbox.
     * 
     * @param mailbox The mailbox to alter.
     * @param acl     The particular ACL to revoke.
     * 
     * @exception MessagingException
     */
    public synchronized void removeACLRights(String mailbox, ACL acl) throws MessagingException {
        /*if (!hasCapability("ACL")) {
            throw new MethodNotSupportedException("ACL not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "SETACL");
        command.appendEncodedString(mailbox);
        
        command.appendACL(acl, "-"); 
        
        sendSimpleCommand(command); 
    }
    
    
    /**
     * Get the ACL rights assigned to a given mailbox.
     * 
     * @param mailbox The target mailbox.
     * 
     * @return The an array of ACL items describing the access 
     *         rights to the mailbox.
     * @exception MessagingException
     */
    public synchronized ACL[] getACLRights(String mailbox) throws MessagingException {
        /*if (!hasCapability("ACL")) {
            throw new MethodNotSupportedException("ACL not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "GETACL");
        command.appendEncodedString(mailbox);
    
        // now send the GETACL command, which will return a single ACL untagged response.      
        sendCommand(command); 
        // there should be just a single ACL response back from this command. 
        IMAPACLResponse response = (IMAPACLResponse)extractResponse("ACL"); 
        return response.acls; 
    }
    
    
    /**
     * Get the current user's ACL rights to a given mailbox. 
     * 
     * @param mailbox The target mailbox.
     * 
     * @return The Rights associated with this mailbox. 
     * @exception MessagingException
     */
    public synchronized Rights getMyRights(String mailbox) throws MessagingException {
        /*if (!hasCapability("ACL")) {
            throw new MethodNotSupportedException("ACL not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "MYRIGHTS");
        command.appendEncodedString(mailbox);
    
        // now send the MYRIGHTS command, which will return a single MYRIGHTS untagged response.      
        sendCommand(command); 
        // there should be just a single MYRIGHTS response back from this command. 
        IMAPMyRightsResponse response = (IMAPMyRightsResponse)extractResponse("MYRIGHTS"); 
        return response.rights; 
    }
    
    
    /**
     * List the ACL rights that a particular user has 
     * to a mailbox.
     * 
     * @param mailbox The target mailbox.
     * @param name    The user we're querying.
     * 
     * @return An array of rights the use has to this mailbox. 
     * @exception MessagingException
     */
    public synchronized Rights[] listACLRights(String mailbox, String name) throws MessagingException {
        /*if (!hasCapability("ACL")) {
            throw new MethodNotSupportedException("ACL not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "LISTRIGHTS");
        command.appendEncodedString(mailbox);
        command.appendString(name); 
    
        // now send the GETACL command, which will return a single ACL untagged response.      
        sendCommand(command); 
        // there should be just a single ACL response back from this command. 
        IMAPListRightsResponse response = (IMAPListRightsResponse)extractResponse("LISTRIGHTS"); 
        return response.rights; 
    }
    
    
    /**
     * Delete an ACL item for a given user name from 
     * a target mailbox. 
     * 
     * @param mailbox The mailbox we're altering.
     * @param name    The user name.
     * 
     * @exception MessagingException
     */
    public synchronized void deleteACL(String mailbox, String name) throws MessagingException {
        /*if (!hasCapability("ACL")) {
            throw new MethodNotSupportedException("ACL not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "DELETEACL");
        command.appendEncodedString(mailbox);
        command.appendString(name); 
    
        // just send the command.  No response to handle. 
        sendSimpleCommand(command); 
    }
    
    /**
     * Fetch the quota root information for a target mailbox.
     * 
     * @param mailbox The mailbox of interest.
     * 
     * @return An array of quotas describing all of the quota roots
     *         that apply to the target mailbox.
     * @exception MessagingException
     */
    public synchronized Quota[] fetchQuotaRoot(String mailbox) throws MessagingException {
        /*if (!hasCapability("QUOTA")) {
            throw new MethodNotSupportedException("QUOTA not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "GETQUOTAROOT");
        command.appendEncodedString(mailbox);
    
        // This will return a single QUOTAROOT response, plust a series of QUOTA responses for 
        // each root names in the first response.  
        sendCommand(command); 
        // we don't really need this, but pull it from the response queue anyway. 
        extractResponse("QUOTAROOT"); 
        
        // now get the real meat of the matter 
        List responses = extractResponses("QUOTA"); 
        
        // now copy all of the returned quota items into the response array. 
        Quota[] quotas = new Quota[responses.size()]; 
        for (int i = 0; i < quotas.length; i++) {
            IMAPQuotaResponse q = (IMAPQuotaResponse)responses.get(i); 
            quotas[i] = q.quota; 
        }
        
        return quotas; 
    }
    
    /**
     * Fetch QUOTA information from a named QUOTE root.
     * 
     * @param root   The target root name.
     * 
     * @return An array of Quota items associated with that root name.
     * @exception MessagingException
     */
    public synchronized Quota[] fetchQuota(String root) throws MessagingException {
       /* if (!hasCapability("QUOTA")) {
            throw new MethodNotSupportedException("QUOTA not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "GETQUOTA");
        command.appendString(root);
    
        // This will return a single QUOTAROOT response, plust a series of QUOTA responses for 
        // each root names in the first response.  
        sendCommand(command); 
        
        // now get the real meat of the matter 
        List responses = extractResponses("QUOTA"); 
        
        // now copy all of the returned quota items into the response array. 
        Quota[] quotas = new Quota[responses.size()]; 
        for (int i = 0; i < quotas.length; i++) {
            IMAPQuotaResponse q = (IMAPQuotaResponse)responses.get(i); 
            quotas[i] = q.quota; 
        }
        
        return quotas; 
    }
    
    /**
     * Set a Quota item for the currently accessed 
     * userid/folder resource. 
     * 
     * @param quota  The new QUOTA information.
     * 
     * @exception MessagingException
     */
    public synchronized void setQuota(Quota quota) throws MessagingException {
        /*if (!hasCapability("QUOTA")) {
            throw new MethodNotSupportedException("QUOTA not available from this IMAP server"); 
        }*/
        IMAPCommand command = new IMAPCommand(objId, "GETQUOTA");
        // this gets appended as a list of resource values 
        command.appendQuota(quota); 
    
        // This will return a single QUOTAROOT response, plust a series of QUOTA responses for 
        // each root names in the first response.  
        sendCommand(command); 
        // we don't really need this, but pull it from the response queue anyway. 
        extractResponses("QUOTA"); 
    }
    
    
    /**
     * Test if this connection has a given capability. 
     * 
     * @param capability The capability name.
     * 
     * @return true if this capability is in the list, false for a mismatch. 
     */
    public boolean hasCapability(String capability) {
        if (capabilities == null) {
            return false; 
        }
        return capabilities.containsKey(capability);
    }
    
    /**
     * Tag this connection as having been closed by the 
     * server.  This will not be returned to the 
     * connection pool. 
     */
    public void setClosed() {
        closed = true;
    }
    
    /**
     * Test if the connnection has been forcibly closed.
     * 
     * @return True if the server disconnected the connection.
     */
    public boolean isClosed() {
        return closed; 
    }
    
    public boolean isSocketAlive()
    {
       return socket != null && socket.isConnected();

    }
    public IMAPSearchResponse rawSearch(String cmd, String args) throws MessagingException
    {
        IMAPCommand command = new IMAPCommand(objId, cmd);

       
        // need to append the message set 
        command.appendAtom(args); 

        //reader.setUseRawSearchResonse(true);
        // now issue the composed command.
        sendCommand(command);

        // get the list of search responses 
        IMAPSearchResponse hits = (IMAPSearchResponse)extractResponse("SEARCH"); 
        
        //reader.setUseRawSearchResonse(false);
     // and return the message hits 
        return hits; 
    }
    
    @Override
    protected void getConnectionStreams() throws MessagingException, IOException {
       if(!useCompress)
    	   super.getConnectionStreams();
       else
       {
    	   com.jcraft.jzlib.Inflater inflater = new com.jcraft.jzlib.Inflater(15, true);
    	   com.jcraft.jzlib.InflaterInputStream zInputStream = new com.jcraft.jzlib.InflaterInputStream(socket.getInputStream(), inflater);
    	   com.jcraft.jzlib.Deflater df = new com.jcraft.jzlib.Deflater(1, true);
    	   com.jcraft.jzlib.DeflaterOutputStream zOutputStream = new com.jcraft.jzlib.DeflaterOutputStream(socket.getOutputStream(),df);
           zOutputStream.setSyncFlush(true);
           
//    	   java.util.zip.Inflater inflater = new java.util.zip.Inflater(true);
//    	   java.util.zip.InflaterInputStream zInputStream = new java.util.zip.InflaterInputStream(socket.getInputStream(), inflater);
//    	   
//    	   java.util.zip.Deflater df = new java.util.zip.Deflater(java.util.zip.Deflater.BEST_SPEED, true);
//    	   df.setStrategy(java.util.zip.Deflater.HUFFMAN_ONLY );
//    	   java.util.zip.DeflaterOutputStream zOutputStream = new java.util.zip.DeflaterOutputStream(socket.getOutputStream(), df);
    	  
//           ZInputStream zInputStream = new ZInputStream(socket.getInputStream(), true);
//           zInputStream.setFlushMode(JZlib.Z_PARTIAL_FLUSH);
//           ZOutputStream zOutputStream = new ZOutputStream(socket.getOutputStream(), JZlib.Z_BEST_SPEED, true);
//           zOutputStream.setFlushMode(JZlib.Z_PARTIAL_FLUSH);

//    	   inputStream = zInputStream;
//    	   outputStream = zOutputStream;
    	   
           inputStream = new TraceInputStream(zInputStream, debugStream, debug, props.getBooleanProperty(MAIL_ENCODE_TRACE, false));
           outputStream = new TraceOutputStream(zOutputStream, debugStream, debug, props.getBooleanProperty(MAIL_ENCODE_TRACE, false));

       }
    }

	public void write(String str) throws MessagingException
	{
		try
		{
			outputStream.write(str.getBytes());
		}
		catch (IOException e)
		{
			throw new MessagingException(e.toString(), e);
		}
	}

    public synchronized void setIdleHandler(IMAPUntaggedResponseHandler h) {
        this.idleHandler = h;
    }

}

