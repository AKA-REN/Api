local Maid = {}
Maid.__index = Maid

local function cleaning(env)
    if not env then return end

    local ok, err = pcall(function()
        local t = typeof(env)
        if t == "thread" then
            task.cancel(env)
        elseif t == "RBXScriptConnection" then
            env:Disconnect()
        elseif t == "Instance" then
            env:Destroy()
        elseif t == "table" then
            if type(env.Destroy) == "function" then
                env:Destroy()
            elseif type(env.Disconnect) == "function" then
                env:Disconnect()
            elseif type(env.Remove) == "function" then
                env:Remove()
            end
        end
    end)

    if not ok then
        warn("[Maid] cleanup error:", err)
    end
end

function Maid.new()
    return setmetatable({ _tasks = {} }, Maid)
end

function Maid:GiveTask(task_obj, key)
    if not task_obj then
        warn("[Maid] GiveTask: nil task")
        return
    end

    if key ~= nil then
        if type(key) ~= "string" then
            warn("[Maid] GiveTask: key must be string")
            return
        end
        local old = self._tasks[key]
        if old then cleaning(old) end
        self._tasks[key] = task_obj
        return task_obj
    end

    table.insert(self._tasks, task_obj)
    return task_obj
end

function Maid:GetTasks()
    return self._tasks
end

function Maid:RemoveTask(key)
    local t = self._tasks[key]
    if t then
        cleaning(t)
        if type(key) == "number" then
            table.remove(self._tasks, key)
        else
            self._tasks[key] = nil
        end
    end
end

function Maid:ClearTasks()
    for _, env in next, self._tasks do
        cleaning(env)
    end
    table.clear(self._tasks)
end

return Maid
