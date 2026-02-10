-- Ai Vibe Code

getgenv().network = getgenv().network or (function()
    local network = {}

    local remoteCache = {}
    local connections = {}
    local invokeRemotes = {}

    local function resolveRemote(name)
        if typeof(name) == "Instance" then
            return name
        end

        if remoteCache[name] then
            return remoteCache[name]
        end

        local found = game:FindFirstChild(name, true)
        if found then
            remoteCache[name] = found
        end

        return found
    end

    local function trackConnection(conn)
        connections[#connections + 1] = conn
    end

    local function isValidRemote(remote)
        return remote
            and typeof(remote) == "Instance"
            and (remote:IsA("RemoteEvent") or remote:IsA("RemoteFunction"))
    end

    function network:Retrieve(name, callback)
        assert(callback and type(callback) == "function", "[Network] callback must be a function")

        local remote = resolveRemote(name)
        if not remote or not isValidRemote(remote) then
            warn("[Network] Invalid or missing remote:", tostring(name))
            return nil
        end

        if type(name) == "string" then
            remoteCache[name] = remote
        end

        if remote:IsA("RemoteEvent") then
            local conn = remote.OnClientEvent:Connect(callback)
            trackConnection(conn)
            return conn
        elseif remote:IsA("RemoteFunction") then
            remote.OnClientInvoke = callback
            invokeRemotes[#invokeRemotes + 1] = remote
            return remote
        end
    end

    function network:Send(name, ...)
        local remote = resolveRemote(name)
        if not remote or not isValidRemote(remote) then
            warn("[Network] Invalid or missing remote:", tostring(name))
            return nil
        end

        if remote:IsA("RemoteEvent") then
            remote:FireServer(...)
        elseif remote:IsA("RemoteFunction") then
            return remote:InvokeServer(...)
        end
    end

    function network:SendSafe(name, ...)
        local ok, result = pcall(self.Send, self, name, ...)
        if not ok then
            warn("[Network] SendSafe failed:", result)
            return nil
        end
        return result
    end

    function network:GetRemote(name)
        return resolveRemote(name)
    end

    function network:Disconnect()
        for i = #connections, 1, -1 do
            local conn = connections[i]
            if typeof(conn) == "RBXScriptConnection" and conn.Connected then
                conn:Disconnect()
            end
            connections[i] = nil
        end

        for i = #invokeRemotes, 1, -1 do
            local remote = invokeRemotes[i]
            if remote and remote:IsA("RemoteFunction") then
                remote.OnClientInvoke = nil
            end
            invokeRemotes[i] = nil
        end

        table.clear(remoteCache)
    end

    function network:RemoveRemote(name)
        if type(name) == "string" then
            remoteCache[name] = nil
        end
    end

    return network
end)()

return getgenv().network
